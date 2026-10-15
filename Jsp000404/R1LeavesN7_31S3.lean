import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_31S0
import Jsp000404.R1LeavesN7_31S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2852 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4209 | h4209
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4210 | h4210
    · linarith only [h2852, h4210, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4212 | h4212
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4213 | h4213
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4214 | h4214
          · linarith only [h2852, h4209, h4214, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4216 | h4216
            · linarith only [h2852, h4213, h4216, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4218 | h4218
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4219 | h4219
                · linarith only [h4210, h4216, h4219, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4221 | h4221
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4222 | h4222
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4223 | h4223
                      · linarith only [h4213, h4214, h4216, h4218, h4223, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4225 | h4225
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4226 | h4226
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4227 | h4227
                            · linarith only [h4209, h4227, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4229 | h4229
                              · linarith only [h0, h4219, h4227, h4229, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h0bigk with h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c | h4231c
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h0, hlam, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h2249, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h2576, hlam, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h2850, hlam, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h0, h4219, hc01, hc25, hlam, hphi, ht12, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h2852, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h0, h4219, h4227, hc04, hc45, hlam, hphi, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4210, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  rcases p4231_3 (m.d 0 1) (by simp) with h4242 | h4242
                                  · linarith only [h2249, h4242, hlam]
                                  · rcases p4231_3 (m.d 0 2) (by simp) with h4244 | h4244
                                    · linarith only [h2852, h4244, hlam]
                                    · linarith only [h0, h4244, hlam]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  rcases p4231_3 (m.d 0 1) (by simp) with h4247 | h4247
                                  · linarith only [h2249, h4247, hlam]
                                  · rcases p4231_3 (m.d 0 2) (by simp) with h4249 | h4249
                                    · linarith only [h2852, h4249, hlam]
                                    · rcases p4231_3 (m.d 0 3) (by simp) with h4251 | h4251
                                      · rcases p4231_3 (m.d 0 4) (by simp) with h4252 | h4252
                                        · linarith only [h4212, h4252, hlam]
                                        · rcases p4231_3 (m.d 0 5) (by simp) with h4254 | h4254
                                          · linarith only [h4213, h4254, hlam]
                                          · linarith only [h4210, h4254, hlam]
                                      · linarith only [h2852, h4251, hlam]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  rcases p4231_3 (m.d 0 1) (by simp) with h4259 | h4259
                                  · linarith only [h2249, h4259, hlam]
                                  · rcases p4231_3 (m.d 0 2) (by simp) with h4261 | h4261
                                    · linarith only [h2852, h4261, hlam]
                                    · linarith only [h4209, h4261, hlam]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h2249, h4213, h4216, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4231_1, u5ehi3]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h0, h4209, h4219, h4227, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4209, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4212, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4214, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  rcases p4231_3 (m.d 0 1) (by simp) with h4270 | h4270
                                  · linarith only [h2850, h4270, hlam]
                                  · rcases p4231_3 (m.d 0 2) (by simp) with h4272 | h4272
                                    · linarith only [h4210, h4272, hlam]
                                    · linarith only [h0, h4272, hlam]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4209, h4210, h4227, hc24, hc45, hlam, hphi, p4231_1]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [h4213, hlam, p4231_0]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  rcases p4231_3 (m.d 0 1) (by simp) with h4277 | h4277
                                  · linarith only [h2850, h4277, hlam]
                                  · rcases p4231_3 (m.d 0 2) (by simp) with h4279 | h4279
                                    · linarith only [h4210, h4279, hlam]
                                    · linarith only [h4209, h4279, hlam]
                                · have p4231_0 := h4231c.1
                                  have p4231_1 := h4231c.2.1
                                  have p4231_2 := h4231c.2.2.1
                                  have p4231_3 := h4231c.2.2.2
                                  linarith only [hlam, p4231_0]
                          · linarith only [h2249, h4213, h4216, h4226, hlam]
                        · linarith only [h2249, h4213, h4216, h4225, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h2249, h4213, h4222, hlam]
                  · linarith only [h2249, h4212, h4213, h4221, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h4209, h4218, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4288 | h4288
          · linarith only [h2852, h4209, h4213, h4288, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4290 | h4290
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4291 | h4291
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4292 | h4292
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4293 | h4293
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4294 | h4294
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4295 | h4295
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4296 | h4296
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4297 | h4297
                          · linarith only [h2852, h4209, h4213, h4290, h4296, h4297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h2852, h4209, h4294, h4296, h4297, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2852, h4212, h4296, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4301 | h4301
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4302 | h4302
                          · linarith only [h4290, h4302, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h2852, h4209, h4290, h4294, h4301, h4302, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h2852, h4212, h4301, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4306 | h4306
                      · linarith only [h4288, h4293, h4294, h4306, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4308 | h4308
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4309 | h4309
                          · linarith only [h2249, h4294, h4309, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4311 | h4311
                            · linarith only [h2852, h4209, h4290, h4306, h4311, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4313 | h4313
                              · linarith only [h4212, h4213, h4306, h4313, hc05, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · linarith only [h2852, h4209, h4290, h4294, h4308, h4313, hc34, hc45, hlam, hphi]
                        · linarith only [h2852, h4209, h4212, h4308, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h2249, h2852, h4209, h4212, h4290, h4293, hc01, hc12, hlam, hphi]
                · linarith only [h2852, h4290, h4292, hc02, hc25, hlam, hphi]
              · linarith only [h2852, h4209, h4290, h4291, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4320 | h4320
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4321 | h4321
                · linarith only [h4209, h4210, h4290, h4321, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4323 | h4323
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4324 | h4324
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4325 | h4325
                      · linarith only [h4320, h4321, h4325, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4327 | h4327
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4328 | h4328
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4329 | h4329
                            · linarith only [h2852, h4209, h4213, h4324, h4325, h4329, hc13, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4331 | h4331
                              · linarith only [h0, h4321, h4329, h4331, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases h0bigk with h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c | h4333c
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h0, hlam, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2249, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2576, hlam, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2850, hlam, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2852, h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2852, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2576, h2852, h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4210, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4213, h4290, h4324, hc02, hc23, hlam, hphi, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2576, h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4213, hlam, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2576, h4320, h4321, hc01, hc25, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4209, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4212, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4288, hlam, p4333_0]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h4209, h4210, h4327, h4329, hc34, hc45, hlam, hphi, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2852, h4209, h4213, h4290, h4324, h4327, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [h2576, h4213, h4290, h4324, hc01, hc23, hlam, hphi, ht12, p4333_1]
                                · have p4333_0 := h4333c.1
                                  have p4333_1 := h4333c.2.1
                                  have p4333_2 := h4333c.2.2.1
                                  have p4333_3 := h4333c.2.2.2
                                  linarith only [hlam, p4333_0]
                          · linarith only [h4290, h4324, h4328, hlam]
                        · linarith only [h4213, h4290, h4324, h4327, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4361 | h4361
                      · linarith only [h4290, h4320, h4361, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4363 | h4363
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4364 | h4364
                          · linarith only [h0, h4290, h4324, h4364, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h2576, h4290, h4320, h4364, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h2576, h4290, h4320, h4363, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h2249, h4212, h4323, hlam]
              · linarith only [h0, h4209, h4320, hlam]
      · linarith only [h2852, h4209, h4212, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h4371 | h4371
    · linarith only [h4209, h4371, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4373 | h4373
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4374 | h4374
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4375 | h4375
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4376 | h4376
            · linarith only [h2852, h4374, h4376, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4378 | h4378
              · linarith only [h4209, h4376, h4378, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4380 | h4380
                · linarith only [h4371, h4374, h4376, h4380, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4382 | h4382
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4383 | h4383
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4384 | h4384
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4385 | h4385
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4386 | h4386
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4387 | h4387
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4388 | h4388
                              · linarith only [h4373, h4388, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h0bigk with h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c | h4390c
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h0, hlam, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2249, hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2576, hlam, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2850, hlam, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h0, h4380, h4385, h4387, hc01, hc23, hlam, hphi, ht12, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2852, hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4209, hlam, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4371, hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4401 | h4401
                                  · linarith only [h2249, h4401, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4403 | h4403
                                    · linarith only [h2852, h4403, hlam]
                                    · linarith only [h0, h4403, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4406 | h4406
                                  · linarith only [h2249, h4406, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4408 | h4408
                                    · linarith only [h2852, h4408, hlam]
                                    · rcases p4390_3 (m.d 0 3) (by simp) with h4410 | h4410
                                      · rcases p4390_3 (m.d 0 4) (by simp) with h4411 | h4411
                                        · linarith only [h4373, h4411, hlam]
                                        · linarith only [h4209, h4411, hlam]
                                      · linarith only [h2852, h4410, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2249, h4375, h4376, h4388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4390_1, u5ehi3]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h2249, h4375, h4376, h4388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4390_1, u5ehi3]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4418 | h4418
                                  · linarith only [h2576, h4418, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4420 | h4420
                                    · linarith only [h4209, h4420, hlam]
                                    · linarith only [h0, h4420, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4423 | h4423
                                  · linarith only [h2576, h4423, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4425 | h4425
                                    · linarith only [h4209, h4425, hlam]
                                    · rcases p4390_3 (m.d 0 3) (by simp) with h4427 | h4427
                                      · rcases p4390_3 (m.d 0 4) (by simp) with h4428 | h4428
                                        · rcases p4390_3 (m.d 0 5) (by simp) with h4429 | h4429
                                          · linarith only [h4375, h4429, hlam]
                                          · linarith only [h4371, h4429, hlam]
                                        · linarith only [h4209, h4428, hlam]
                                      · linarith only [h2852, h4427, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4373, hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4375, h4388, hc04, hlam, hphi, ht0b, ht5b, p4390_1, u5ehi3]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4437 | h4437
                                  · linarith only [h2850, h4437, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4439 | h4439
                                    · linarith only [h4371, h4439, hlam]
                                    · linarith only [h0, h4439, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  rcases p4390_3 (m.d 0 1) (by simp) with h4442 | h4442
                                  · linarith only [h2850, h4442, hlam]
                                  · rcases p4390_3 (m.d 0 2) (by simp) with h4444 | h4444
                                    · linarith only [h4371, h4444, hlam]
                                    · rcases p4390_3 (m.d 0 3) (by simp) with h4446 | h4446
                                      · rcases p4390_3 (m.d 0 4) (by simp) with h4447 | h4447
                                        · rcases p4390_3 (m.d 0 5) (by simp) with h4448 | h4448
                                          · rcases h2bigk with h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c | h4449c
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h0, hlam, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h2852, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4209, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4371, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4380, h4385, h4387, hc02, hc23, hlam, hphi, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4376, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4378, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4380, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              rcases p4449_3 (m.d 0 2) (by simp) with h4460 | h4460
                                              · linarith only [h4460, hlam, p4449_0]
                                              · rcases p4449_3 (m.d 1 2) (by simp) with h4462 | h4462
                                                · linarith only [h4376, h4462, hlam]
                                                · linarith only [h0, h4462, hlam]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4387, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4449_1, u5ehi2]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h2850, h4380, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4449_1, u5ehi0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              rcases p4449_3 (m.d 0 2) (by simp) with h4469 | h4469
                                              · linarith only [h4469, hlam, p4449_0]
                                              · rcases p4449_3 (m.d 1 2) (by simp) with h4471 | h4471
                                                · linarith only [h4378, h4471, hlam]
                                                · linarith only [h0, h4471, hlam]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4385, hlam, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h0, h2850, h4380, h4385, hc01, hc23, hlam, hphi, ht12, p4390_1, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              rcases p4449_3 (m.d 0 2) (by simp) with h4478 | h4478
                                              · linarith only [h4478, hlam, p4449_0]
                                              · rcases p4449_3 (m.d 1 2) (by simp) with h4480 | h4480
                                                · linarith only [h4380, h4480, hlam]
                                                · linarith only [h0, h4480, hlam]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4386, hlam, p4449_1]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [h4387, hlam, p4449_0]
                                            · have p4449_0 := h4449c.1
                                              have p4449_1 := h4449c.2.1
                                              have p4449_2 := h4449c.2.2.1
                                              have p4449_3 := h4449c.2.2.2
                                              linarith only [hlam, p4449_0]
                                          · linarith only [h4371, h4448, hlam]
                                        · linarith only [h4209, h4447, hlam]
                                      · linarith only [h2852, h4446, hlam]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4374, hlam, p4390_0]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [h4375, hlam, p4390_1]
                                · have p4390_0 := h4390c.1
                                  have p4390_1 := h4390c.2.1
                                  have p4390_2 := h4390c.2.2.1
                                  have p4390_3 := h4390c.2.2.2
                                  linarith only [hlam, p4390_0]
                            · linarith only [h4209, h4375, h4387, hlam]
                          · linarith only [h2249, h4373, h4375, h4376, h4386, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h2249, h4373, h4375, h4376, h4385, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h2576, h4375, h4384, hlam]
                    · linarith only [h2249, h4374, h4383, hlam]
                  · linarith only [h2249, h4373, h4382, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4499 | h4499
            · linarith only [h2852, h4374, h4499, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4501 | h4501
              · linarith only [h0, h4209, h4499, h4501, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4503 | h4503
                · linarith only [h4499, h4503, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4505 | h4505
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4506 | h4506
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4507 | h4507
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4508 | h4508
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4509 | h4509
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4510 | h4510
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4511 | h4511
                              · linarith only [h4373, h4375, h4511, hlam]
                              · rcases h0bigk with h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c | h4513c
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h2249, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h2576, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h2850, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, h4503, h4508, h4510, hc01, hc23, hlam, hphi, ht12, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h2852, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4209, hlam, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4371, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  rcases p4513_3 (m.d 0 1) (by simp) with h4524 | h4524
                                  · linarith only [h2249, h4524, hlam]
                                  · rcases p4513_3 (m.d 0 2) (by simp) with h4526 | h4526
                                    · linarith only [h2852, h4526, hlam]
                                    · linarith only [h0, h4526, hlam]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  rcases p4513_3 (m.d 0 1) (by simp) with h4529 | h4529
                                  · linarith only [h2249, h4529, hlam]
                                  · rcases p4513_3 (m.d 0 2) (by simp) with h4531 | h4531
                                    · linarith only [h2852, h4531, hlam]
                                    · rcases p4513_3 (m.d 0 3) (by simp) with h4533 | h4533
                                      · rcases p4513_3 (m.d 0 4) (by simp) with h4534 | h4534
                                        · linarith only [h4373, h4534, hlam]
                                        · linarith only [h4209, h4534, hlam]
                                      · linarith only [h2852, h4533, hlam]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  rcases p4513_3 (m.d 0 1) (by simp) with h4539 | h4539
                                  · linarith only [h2249, h4539, hlam]
                                  · rcases p4513_3 (m.d 0 2) (by simp) with h4541 | h4541
                                    · linarith only [h2852, h4541, hlam]
                                    · rcases p4513_3 (m.d 0 3) (by simp) with h4543 | h4543
                                      · rcases p4513_3 (m.d 0 4) (by simp) with h4544 | h4544
                                        · linarith only [h4373, h4544, hlam]
                                        · rcases p4513_3 (m.d 0 5) (by simp) with h4546 | h4546
                                          · linarith only [h4374, h4546, hlam]
                                          · linarith only [h4375, h4546, hlam]
                                      · linarith only [h4373, h4543, hlam]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4374, hc03, hlam, hphi, ht0b, ht5b, p4513_1, u5ehi3]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4375, h4499, h4505, h4507, hc01, hc23, hlam, hphi, ht12, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4375, h4499, h4505, h4507, hc02, hc23, hlam, hphi, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4373, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4375, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4375, h4499, h4505, h4507, hc01, hc23, hlam, hphi, ht12, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h0, h4375, h4499, h4505, h4507, hc01, hc23, hlam, hphi, ht12, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h4374, hlam, p4513_0]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [h2576, h4375, h4499, h4505, h4507, hc01, hc23, hlam, hphi, ht12, p4513_1]
                                · have p4513_0 := h4513c.1
                                  have p4513_1 := h4513c.2.1
                                  have p4513_2 := h4513c.2.2.1
                                  have p4513_3 := h4513c.2.2.2
                                  linarith only [hlam, p4513_0]
                            · linarith only [h0, h4209, h4499, h4505, h4507, h4510, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h2249, h4374, h4499, h4509, hlam]
                        · linarith only [h4373, h4374, h4375, h4499, h4505, h4507, h4508, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4564 | h4564
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4565 | h4565
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4566 | h4566
                            · linarith only [h2576, h4507, h4566, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h4501, h4566, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h2249, h4374, h4499, h4565, hlam]
                        · linarith only [h2249, h4373, h4374, h4499, h4564, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h2249, h4374, h4506, hlam]
                  · linarith only [h2249, h4373, h4374, h4505, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4573 | h4573
          · linarith only [h4373, h4374, h4573, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4575 | h4575
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4576 | h4576
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4577 | h4577
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4578 | h4578
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4579 | h4579
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4580 | h4580
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4581 | h4581
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4582 | h4582
                          · linarith only [h4373, h4374, h4575, h4582, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h2852, h4575, h4579, h4582, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2249, h2852, h4373, h4575, h4581, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4586 | h4586
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4587 | h4587
                          · linarith only [h4373, h4374, h4575, h4587, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h2852, h4575, h4579, h4587, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2249, h2852, h4373, h4575, h4586, hc01, hc12, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4591 | h4591
                      · linarith only [h4578, h4579, h4591, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4593 | h4593
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4594 | h4594
                          · linarith only [h0, h4209, h4576, h4578, h4579, h4594, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4596 | h4596
                            · linarith only [h4576, h4591, h4596, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4598 | h4598
                              · linarith only [h0, h2852, h4209, h4373, h4575, h4576, h4579, h4591, h4598, hc01, hc35, hlam, hphi, ht12, ht23]
                              · rcases h0bigk with h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c | h4600c
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h0, hlam, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2249, hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2576, hlam, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2850, hlam, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4209, h4576, hc01, hc14, hlam, hphi, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2852, hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4209, hlam, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4371, hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2852, h4575, h4579, h4598, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2852, h4575, h4579, h4598, hc02, hc45, hlam, hphi, ht23, ht34, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2852, h4575, h4579, h4598, hc04, hc45, hlam, hphi, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4374, hlam, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2852, h4373, h4575, h4579, h4598, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h0, h2852, h4373, h4575, h4579, h4598, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4373, hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4573, hlam, p4600_0]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4371, h4577, hc01, hc12, hlam, hphi, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h0, h4371, h4577, hc01, hc12, hlam, hphi, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h4371, h4373, h4577, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [h2576, h4371, h4577, hc01, hc12, hlam, hphi, p4600_1]
                                · have p4600_0 := h4600c.1
                                  have p4600_1 := h4600c.2.1
                                  have p4600_2 := h4600c.2.2.1
                                  have p4600_3 := h4600c.2.2.2
                                  linarith only [hlam, p4600_0]
                        · linarith only [h0, h2249, h2852, h4373, h4593, hc01, hc13, hlam, hphi]
                  · linarith only [h2249, h4373, h4578, hlam]
                · linarith only [h0, h2852, h4575, h4577, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h2852, h4575, h4576, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4630 | h4630
              · linarith only [h0, h4209, h4575, h4630, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4632 | h4632
                · linarith only [h4575, h4632, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4634 | h4634
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4635 | h4635
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4636 | h4636
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4637 | h4637
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4638 | h4638
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4639 | h4639
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4640 | h4640
                              · linarith only [h4373, h4374, h4573, h4575, h4635, h4640, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                              · rcases h0bigk with h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c | h4642c
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, hlam, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h2249, hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h2576, hlam, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h2850, hlam, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, h4632, h4637, h4639, hc01, hc23, hlam, hphi, ht12, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h2852, hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4209, hlam, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4371, hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4374, h4636, h4640, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, h4209, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4374, hlam, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4373, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, h4373, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4373, hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4573, hlam, p4642_0]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h2249, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [h0, h4209, h4374, h4636, h4640, hc01, hc14, hlam, hphi, p4642_1]
                                · have p4642_0 := h4642c.1
                                  have p4642_1 := h4642c.2.1
                                  have p4642_2 := h4642c.2.2.1
                                  have p4642_3 := h4642c.2.2.2
                                  linarith only [hlam, p4642_0]
                            · linarith only [h4630, h4636, h4639, hlam]
                          · linarith only [h4575, h4635, h4638, hlam]
                        · linarith only [h4373, h4575, h4635, h4637, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4671 | h4671
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4672 | h4672
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4673 | h4673
                            · linarith only [h0, h4630, h4636, h4673, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h4630, h4673, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h4575, h4635, h4672, hlam]
                        · linarith only [h4373, h4374, h4575, h4635, h4671, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4678 | h4678
                      · linarith only [h4634, h4635, h4678, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4680 | h4680
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4681 | h4681
                          · linarith only [h0, h4630, h4634, h4635, h4681, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h4575, h4681, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h4373, h4575, h4680, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h2249, h4373, h4634, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h4686 | h4686
        · linarith only [h4373, h4686, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h4688 | h4688
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4689 | h4689
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4690 | h4690
              · linarith only [h4209, h4688, h4690, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · linarith only [h0, h2852, h4689, h4690, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4693 | h4693
              · linarith only [h0, h4209, h4689, h4693, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4695 | h4695
                · linarith only [h4689, h4695, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4697 | h4697
                  · linarith only [h4373, h4688, h4697, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4699 | h4699
                    · linarith only [h4686, h4697, h4699, hc03, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4701 | h4701
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4702 | h4702
                        · linarith only [h0, h4689, h4697, h4702, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4689, h4702, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h2576, h4688, h4701, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h4706 | h4706
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4707 | h4707
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4708 | h4708
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4709 | h4709
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4710 | h4710
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4711 | h4711
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4712 | h4712
                        · linarith only [h0, h2852, h4373, h4706, h4712, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2852, h4706, h4709, h4712, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4715 | h4715
                        · linarith only [h0, h2852, h4373, h4706, h4715, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2852, h4709, h4711, h4715, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h0, h2852, h4373, h4709, h4710, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4719 | h4719
                    · linarith only [h4709, h4719, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4721 | h4721
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4722 | h4722
                        · linarith only [h2249, h4709, h4722, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4724 | h4724
                          · linarith only [h4706, h4719, h4724, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4726 | h4726
                            · linarith only [h4688, h4707, h4726, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · linarith only [h0, h4209, h4721, h4726, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4729 | h4729
                        · linarith only [h0, h2852, h4373, h4706, h4719, h4729, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4731 | h4731
                          · linarith only [h4686, h4706, h4731, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4733 | h4733
                            · linarith only [h2249, h4709, h4721, h4733, hc01, hc24, hlam, hphi, ht12]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4735 | h4735
                              · linarith only [h0, h2852, h4706, h4709, h4721, h4735, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h2852, h4706, h4709, h4735, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h2852, h4706, h4708, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h2852, h4706, h4707, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h4740 | h4740
              · linarith only [h0, h4209, h4706, h4740, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h4742 | h4742
                · linarith only [h4706, h4742, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h4744 | h4744
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4745 | h4745
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4746 | h4746
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4747 | h4747
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4748 | h4748
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4749 | h4749
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h4750 | h4750
                              · linarith only [h0, h2852, h4373, h4688, h4744, h4750, hc01, hc13, hlam, hphi]
                              · linarith only [h0, h2852, h4373, h4746, h4750, hc01, hc14, hlam, hphi]
                            · linarith only [h4740, h4746, h4749, hlam]
                          · linarith only [h4740, h4746, h4747, h4748, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h0, h4706, h4747, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4756 | h4756
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h4757 | h4757
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h4758 | h4758
                            · linarith only [h2576, h4746, h4758, hc01, hc24, hlam, hphi, ht12]
                            · linarith only [h0, h4740, h4758, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h2852, h4745, h4757, hc01, hc13, hlam, hphi]
                        · linarith only [h4706, h4745, h4756, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h0, h2852, h4373, h4744, h4745, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h4764 | h4764
                    · linarith only [h4744, h4764, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h4766 | h4766
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4767 | h4767
                        · linarith only [h2249, h4744, h4767, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4706, h4767, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h4770 | h4770
                        · linarith only [h0, h4706, h4744, h4770, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h4706, h4770, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2850 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h2852 | h2852
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850 h2852

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2576 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h2850 | h2850
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576 h2850

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2249 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h2576 | h2576
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x0 m hb0 hb2 hb3 hb5 hg0 h2249 h2576
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1_x1 m hb0 hb2 hb3 hb5 hg0 h2249 h2576

set_option maxHeartbeats 5048000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h2249 | h2249
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x0 m hb0 hb2 hb3 hb5 hg0 h2249
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_R_s0_x1 m hb0 hb2 hb3 hb5 hg0 h2249

end R2N4
