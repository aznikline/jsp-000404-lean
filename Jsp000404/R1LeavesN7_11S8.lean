import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_11S6
import Jsp000404.R1LeavesN7_11S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9616000 in
set_option maxHeartbeats 9616000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h3620 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 5 (by decide) (by decide) with h4206 | h4206
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4207 | h4207
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4208 | h4208
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4209 | h4209
        · linarith only [h4209, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4211 | h4211
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4212 | h4212
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4213 | h4213
              · linarith only [h4213, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4215 | h4215
                · linarith only [h0, h3, h3620, h4206, h4211, h4213, h4215, h8, hc01, hlam, hphi, u0ehi3]
                · rcases h2bigk with h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c | h4217c
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    rcases p4217_3 (m.d 0 2) (by simp) with h4219 | h4219
                    · rcases p4217_3 (m.d 1 2) (by simp) with h4220 | h4220
                      · linarith only [h0, h4220, hlam]
                      · rcases p4217_3 (m.d 2 3) (by simp) with h4222 | h4222
                        · linarith only [h3, h4222, hlam]
                        · linarith only [h3620, h4222, hlam]
                    · linarith only [h0, h4219, hlam]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h0, h3620, h4206, h4213, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3, h3620, h4206, h4213, hlam, p4217_2]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3, h3620, h4206, hlam, p4217_2]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h0, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3620, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3, h3620, h4211, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3, h3620, h4211, h4213, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h3, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h0, h3, h4206, h4211, h4213, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    rcases p4217_3 (m.d 0 2) (by simp) with h4237 | h4237
                    · rcases p4217_3 (m.d 1 2) (by simp) with h4238 | h4238
                      · linarith only [h3620, h4238, hlam]
                      · linarith only [h4206, h4213, h4238, hlam]
                    · linarith only [h4, h4237, hlam]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    rcases p4217_3 (m.d 0 2) (by simp) with h4242 | h4242
                    · rcases p4217_3 (m.d 1 2) (by simp) with h4243 | h4243
                      · linarith only [h3620, h4243, hlam]
                      · linarith only [h4206, h4243, hlam]
                    · linarith only [h4242, h5, hlam]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4206, h4213, hlam, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4211, hlam, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4213, hlam, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h5, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4206, hlam, p4217_0]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h4212, hlam, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [h0, h4206, h4211, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4217_1]
                  · have p4217_0 := h4217c.1
                    have p4217_1 := h4217c.2.1
                    have p4217_2 := h4217c.2.2.1
                    have p4217_3 := h4217c.2.2.2
                    linarith only [hlam, p4217_0]
            · linarith only [h3620, h4206, h4208, h4212, hlam]
          · linarith only [h0, h3, h3620, h4206, h4211, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h3620, h4206, h4208, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4260 | h4260
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4261 | h4261
        · linarith only [h4207, h4260, h4261, h6, h8, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h3620, h4206, h4207, h4261, hlam]
      · linarith only [h3620, h4206, h4260, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h4265 | h4265
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4266 | h4266
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4267 | h4267
        · linarith only [h4267, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4269 | h4269
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4270 | h4270
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4271 | h4271
              · linarith only [h4271, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4273 | h4273
                · linarith only [h4265, h4273, h8, hc13, hlam, hphi, ht01, u0ehi3]
                · rcases h2bigk with h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c | h4275c
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4277 | h4277
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4278 | h4278
                      · linarith only [h0, h4278, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4280 | h4280
                        · linarith only [h3, h4280, hlam]
                        · linarith only [h3620, h4280, hlam]
                    · linarith only [h0, h4277, hlam]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4284 | h4284
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4285 | h4285
                      · linarith only [h0, h4285, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4287 | h4287
                        · linarith only [h4287, hlam, p4275_0]
                        · rcases p4275_3 (m.d 2 4) (by simp) with h4289 | h4289
                          · linarith only [h4, h4289, hlam]
                          · rcases p4275_3 (m.d 2 5) (by simp) with h4291 | h4291
                            · linarith only [h4291, h5, hlam]
                            · rcases h3bigk with h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c | h4293c
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                rcases p4293_3 (m.d 0 3) (by simp) with h4295 | h4295
                                · rcases p4293_3 (m.d 1 3) (by simp) with h4296 | h4296
                                  · linarith only [h1, h4296, hlam]
                                  · rcases p4293_3 (m.d 2 3) (by simp) with h4298 | h4298
                                    · linarith only [h3, h4298, hlam]
                                    · linarith only [h3620, h4298, hlam]
                                · linarith only [h1, h4295, hlam]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                rcases p4293_3 (m.d 0 3) (by simp) with h4302 | h4302
                                · rcases p4293_3 (m.d 1 3) (by simp) with h4303 | h4303
                                  · linarith only [h1, h4303, hlam]
                                  · rcases p4293_3 (m.d 2 3) (by simp) with h4305 | h4305
                                    · linarith only [h3, h4305, hlam]
                                    · rcases p4293_3 (m.d 3 4) (by simp) with h4307 | h4307
                                      · linarith only [h4307, h6, hlam]
                                      · rcases p4293_3 (m.d 3 5) (by simp) with h4309 | h4309
                                        · linarith only [h4309, h7, hlam]
                                        · rcases h5bigk with h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c | h4311c
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4267, h8, hc14, hc45, hlam, hphi, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4206, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4273, h8, hc34, hc45, hlam, hphi, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h8, hlam, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h2, hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4206, hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h2, h4273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4267, hlam, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h5, hlam, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h3, h4270, hc02, hc15, hlam, hphi, ht0b, ht5b, p4293_1, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h0, h3, h4270, h4273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4293_1, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4271, hlam, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h7, hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4266, hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4270, hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [hlam, p4311_0]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4273, hlam, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h0, h3, h4206, h4270, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4293_1, p4311_1, u0ehi4]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4206, hc12, hc45, hlam, hphi, ht23, ht34, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4206, hc12, hc45, hlam, hphi, ht23, ht34, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [h4273, hc34, hc45, hlam, hphi, p4311_1]
                                          · have p4311_0 := h4311c.1
                                            have p4311_1 := h4311c.2.1
                                            have p4311_2 := h4311c.2.2.1
                                            have p4311_3 := h4311c.2.2.2
                                            linarith only [hlam, p4311_0]
                                · linarith only [h3, h4302, hlam]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                rcases p4293_3 (m.d 0 3) (by simp) with h4338 | h4338
                                · rcases p4293_3 (m.d 1 3) (by simp) with h4339 | h4339
                                  · linarith only [h1, h4339, hlam]
                                  · linarith only [h4265, h4339, hlam]
                                · linarith only [h4338, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                rcases p4293_3 (m.d 0 3) (by simp) with h4343 | h4343
                                · rcases p4293_3 (m.d 1 3) (by simp) with h4344 | h4344
                                  · linarith only [h1, h4344, hlam]
                                  · linarith only [h4266, h4344, hlam]
                                · linarith only [h4343, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h1, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h3620, hlam, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h0, h3620, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4275_1, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h0, h3620, hc01, hc35, hlam, hphi, ht0b, ht5b, p4275_1, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h3, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4275_1, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h0, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4275_1, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p4275_1, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h6, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h4265, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h4269, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h4273, hlam, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h7, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h4266, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h4270, hlam, p4293_0]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [h1, h4266, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4293_1]
                              · have p4293_0 := h4293c.1
                                have p4293_1 := h4293c.2.1
                                have p4293_2 := h4293c.2.2.1
                                have p4293_3 := h4293c.2.2.2
                                linarith only [hlam, p4293_0]
                    · linarith only [h4284, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4369 | h4369
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4370 | h4370
                      · linarith only [h0, h4370, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4372 | h4372
                        · linarith only [h3, h4372, hlam]
                        · linarith only [h4269, h4372, hlam]
                    · linarith only [h4369, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4376 | h4376
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4377 | h4377
                      · linarith only [h0, h4377, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4379 | h4379
                        · linarith only [h3, h4379, hlam]
                        · linarith only [h4270, h4379, hlam]
                    · linarith only [h4376, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h0, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h3620, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h0, h3, h4206, h4270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4206, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h3, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4389 | h4389
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4390 | h4390
                      · linarith only [h4390, hlam, p4275_0]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4392 | h4392
                        · rcases p4275_3 (m.d 2 4) (by simp) with h4393 | h4393
                          · linarith only [h4269, h4393, hlam]
                          · rcases p4275_3 (m.d 2 5) (by simp) with h4395 | h4395
                            · linarith only [h4270, h4395, hlam]
                            · linarith only [h4206, h4395, hlam]
                        · linarith only [h4392, hlam, p4275_0]
                    · linarith only [h0, h4389, hlam]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4401 | h4401
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4402 | h4402
                      · linarith only [h3620, h4402, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4404 | h4404
                        · rcases p4275_3 (m.d 2 4) (by simp) with h4405 | h4405
                          · linarith only [h4269, h4405, hlam]
                          · rcases p4275_3 (m.d 2 5) (by simp) with h4407 | h4407
                            · linarith only [h4270, h4407, hlam]
                            · linarith only [h4271, h4407, hlam]
                        · linarith only [h4269, h4404, hlam]
                    · linarith only [h4, h4401, hlam]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h0, h3, h4206, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4269, hlam, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4271, hlam, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h5, hlam, p4275_0]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4419 | h4419
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4420 | h4420
                      · linarith only [h4420, hlam, p4275_0]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4422 | h4422
                        · rcases p4275_3 (m.d 2 4) (by simp) with h4423 | h4423
                          · linarith only [h4271, h4423, hlam]
                          · rcases p4275_3 (m.d 2 5) (by simp) with h4425 | h4425
                            · rcases h3bigk with h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c | h4426c
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4428 | h4428
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4429 | h4429
                                  · linarith only [h1, h4429, hlam]
                                  · rcases p4426_3 (m.d 2 3) (by simp) with h4431 | h4431
                                    · linarith only [h3, h4431, hlam]
                                    · linarith only [h3620, h4431, hlam]
                                · linarith only [h1, h4428, hlam]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4270, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4275_1, p4426_1]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4436 | h4436
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4437 | h4437
                                  · linarith only [h1, h4437, hlam]
                                  · linarith only [h4265, h4437, hlam]
                                · linarith only [h4436, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4441 | h4441
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4442 | h4442
                                  · linarith only [h1, h4442, hlam]
                                  · linarith only [h4266, h4442, hlam]
                                · linarith only [h4441, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h1, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h3620, hlam, p4426_1]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4449 | h4449
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4450 | h4450
                                  · rcases p4426_3 (m.d 2 3) (by simp) with h4451 | h4451
                                    · rcases p4426_3 (m.d 3 4) (by simp) with h4452 | h4452
                                      · linarith only [h4452, hlam, p4426_0]
                                      · rcases p4426_3 (m.d 3 5) (by simp) with h4454 | h4454
                                        · linarith only [h4266, h4454, hlam]
                                        · linarith only [h4273, h4454, hlam]
                                    · linarith only [h4269, h4451, hlam]
                                  · linarith only [h4450, hlam, p4426_0]
                                · linarith only [h4449, h6, hlam]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4460 | h4460
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4461 | h4461
                                  · rcases p4426_3 (m.d 2 3) (by simp) with h4462 | h4462
                                    · rcases p4426_3 (m.d 3 4) (by simp) with h4463 | h4463
                                      · linarith only [h4265, h4463, hlam]
                                      · rcases p4426_3 (m.d 3 5) (by simp) with h4465 | h4465
                                        · linarith only [h4465, hlam, p4426_0]
                                        · rcases h5bigk with h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c | h4467c
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4206, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4275_1, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4273, h8, hc34, hc45, hlam, hphi, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h8, hlam, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h2, hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4206, hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h2, h4273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4267, hlam, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h5, hlam, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h0, h3, h4270, hc01, hc15, hlam, hphi, ht0b, ht5b, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h0, h3, h4270, h4273, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4271, hlam, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h7, hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4266, hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4270, hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hlam, p4467_0]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4273, hlam, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p4467_1, u0ehi4]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4206, hc12, hc45, hlam, hphi, ht23, ht34, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hc12, hc45, hlam, hphi, ht23, ht34, p4275_1, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [h4273, hc34, hc45, hlam, hphi, p4467_1]
                                          · have p4467_0 := h4467c.1
                                            have p4467_1 := h4467c.2.1
                                            have p4467_2 := h4467c.2.2.1
                                            have p4467_3 := h4467c.2.2.2
                                            linarith only [hlam, p4467_0]
                                    · linarith only [h4270, h4462, hlam]
                                  · linarith only [h4461, hlam, p4426_0]
                                · linarith only [h4460, h7, hlam]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h3, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h0, h3, h4265, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4426_1]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4499 | h4499
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4500 | h4500
                                  · linarith only [h3620, h4500, hlam]
                                  · linarith only [h4265, h4500, hlam]
                                · linarith only [h4499, h6, hlam]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                rcases p4426_3 (m.d 0 3) (by simp) with h4504 | h4504
                                · rcases p4426_3 (m.d 1 3) (by simp) with h4505 | h4505
                                  · linarith only [h3620, h4505, hlam]
                                  · linarith only [h4266, h4505, hlam]
                                · linarith only [h4504, h7, hlam]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h6, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4265, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4269, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4273, hlam, p4426_1]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h7, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4266, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h4270, hlam, p4426_0]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [h1, h4266, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4426_1]
                              · have p4426_0 := h4426c.1
                                have p4426_1 := h4426c.2.1
                                have p4426_2 := h4426c.2.2.1
                                have p4426_3 := h4426c.2.2.2
                                linarith only [hlam, p4426_0]
                            · linarith only [h4425, hlam, p4275_0]
                        · linarith only [h3620, h4422, hlam]
                    · linarith only [h0, h4419, hlam]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [h4270, hlam, p4275_1]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    rcases p4275_3 (m.d 0 2) (by simp) with h4523 | h4523
                    · rcases p4275_3 (m.d 1 2) (by simp) with h4524 | h4524
                      · linarith only [h4206, h4524, hlam]
                      · rcases p4275_3 (m.d 2 3) (by simp) with h4526 | h4526
                        · rcases p4275_3 (m.d 2 4) (by simp) with h4527 | h4527
                          · linarith only [h4271, h4527, hlam]
                          · rcases p4275_3 (m.d 2 5) (by simp) with h4529 | h4529
                            · rcases h3bigk with h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c | h4530c
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4532 | h4532
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4533 | h4533
                                  · linarith only [h1, h4533, hlam]
                                  · rcases p4530_3 (m.d 2 3) (by simp) with h4535 | h4535
                                    · linarith only [h3, h4535, hlam]
                                    · linarith only [h3620, h4535, hlam]
                                · linarith only [h1, h4532, hlam]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h0, h3, h4270, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4275_1, p4530_1]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4540 | h4540
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4541 | h4541
                                  · linarith only [h1, h4541, hlam]
                                  · linarith only [h4265, h4541, hlam]
                                · linarith only [h4540, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4545 | h4545
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4546 | h4546
                                  · linarith only [h1, h4546, hlam]
                                  · linarith only [h4266, h4546, hlam]
                                · linarith only [h4545, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h1, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h3620, hlam, p4530_1]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4553 | h4553
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4554 | h4554
                                  · rcases p4530_3 (m.d 2 3) (by simp) with h4555 | h4555
                                    · rcases p4530_3 (m.d 3 4) (by simp) with h4556 | h4556
                                      · linarith only [h4556, hlam, p4530_0]
                                      · rcases p4530_3 (m.d 3 5) (by simp) with h4558 | h4558
                                        · linarith only [h4266, h4558, hlam]
                                        · linarith only [h4273, h4558, hlam]
                                    · linarith only [h4269, h4555, hlam]
                                  · linarith only [h4554, hlam, p4530_0]
                                · linarith only [h4553, h6, hlam]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4564 | h4564
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4565 | h4565
                                  · rcases p4530_3 (m.d 2 3) (by simp) with h4566 | h4566
                                    · rcases p4530_3 (m.d 3 4) (by simp) with h4567 | h4567
                                      · linarith only [h4265, h4567, hlam]
                                      · rcases p4530_3 (m.d 3 5) (by simp) with h4569 | h4569
                                        · linarith only [h4569, hlam, p4530_0]
                                        · rcases h5bigk with h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c | h4571c
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4206, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4524, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4275_1, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4273, h8, hc34, hc45, hlam, hphi, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h8, hlam, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h2, hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4206, hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4267, hlam, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h5, hlam, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h0, h3, h4270, hc01, hc15, hlam, hphi, ht0b, ht5b, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h0, h3, h4270, hc01, hc35, hlam, hphi, ht0b, ht5b, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4271, hlam, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h7, hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4266, hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4270, hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [hlam, p4571_0]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4273, hlam, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h0, h3, h4270, h4524, hc01, hc12, hc45, hlam, hphi, ht23, ht34, p4275_1, p4571_1, u0ehi4]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4206, hc12, hc45, hlam, hphi, ht23, ht34, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4524, hc12, hc45, hlam, hphi, ht23, ht34, p4275_1, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [h4273, hc34, hc45, hlam, hphi, p4571_1]
                                          · have p4571_0 := h4571c.1
                                            have p4571_1 := h4571c.2.1
                                            have p4571_2 := h4571c.2.2.1
                                            have p4571_3 := h4571c.2.2.2
                                            linarith only [hlam, p4571_0]
                                    · linarith only [h4270, h4566, hlam]
                                  · linarith only [h4565, hlam, p4530_0]
                                · linarith only [h4564, h7, hlam]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h3, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h0, h3, h4265, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4530_1]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4603 | h4603
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4604 | h4604
                                  · linarith only [h3620, h4604, hlam]
                                  · linarith only [h4265, h4604, hlam]
                                · linarith only [h4603, h6, hlam]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                rcases p4530_3 (m.d 0 3) (by simp) with h4608 | h4608
                                · rcases p4530_3 (m.d 1 3) (by simp) with h4609 | h4609
                                  · linarith only [h3620, h4609, hlam]
                                  · linarith only [h4266, h4609, hlam]
                                · linarith only [h4608, h7, hlam]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h6, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h4265, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h4269, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h4273, hlam, p4530_1]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h7, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h4266, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h4270, hlam, p4530_0]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [h1, h4266, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4530_1]
                              · have p4530_0 := h4530c.1
                                have p4530_1 := h4530c.2.1
                                have p4530_2 := h4530c.2.2.1
                                have p4530_3 := h4530c.2.2.2
                                linarith only [hlam, p4530_0]
                            · linarith only [h4271, h4529, hlam]
                        · linarith only [h4269, h4526, hlam]
                    · linarith only [h4, h4523, hlam]
                  · have p4275_0 := h4275c.1
                    have p4275_1 := h4275c.2.1
                    have p4275_2 := h4275c.2.2.1
                    have p4275_3 := h4275c.2.2.2
                    linarith only [hlam, p4275_0]
            · linarith only [h1, h3620, h4266, h4270, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h3620, h4269, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4629 | h4629
        · linarith only [h0, h3, h4265, h4266, h4629, h7, h8, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4631 | h4631
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4632 | h4632
            · linarith only [h0, h3, h4265, h4266, h4632, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4634 | h4634
              · linarith only [h0, h3, h3620, h4632, h4634, h7, h8, hc01, hc12, hc24, hlam, hphi, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4636 | h4636
                · linarith only [h4265, h4636, h8, hc13, hlam, hphi, ht01, u0ehi3]
                · rcases h2bigk with h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c | h4638c
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h3, h3620, h4632, h7, hlam, p4638_2]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    rcases p4638_3 (m.d 0 2) (by simp) with h4641 | h4641
                    · rcases p4638_3 (m.d 1 2) (by simp) with h4642 | h4642
                      · linarith only [h0, h4642, hlam]
                      · rcases p4638_3 (m.d 2 3) (by simp) with h4644 | h4644
                        · linarith only [h4644, hlam, p4638_0]
                        · rcases p4638_3 (m.d 2 4) (by simp) with h4646 | h4646
                          · linarith only [h4, h4646, hlam]
                          · rcases p4638_3 (m.d 2 5) (by simp) with h4648 | h4648
                            · linarith only [h4648, h5, hlam]
                            · linarith only [h4632, h4648, hlam]
                    · linarith only [h4641, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    rcases p4638_3 (m.d 0 2) (by simp) with h4652 | h4652
                    · rcases p4638_3 (m.d 1 2) (by simp) with h4653 | h4653
                      · linarith only [h0, h4653, hlam]
                      · rcases p4638_3 (m.d 2 3) (by simp) with h4655 | h4655
                        · linarith only [h3, h4655, hlam]
                        · linarith only [h4631, h4655, hlam]
                    · linarith only [h4652, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    rcases p4638_3 (m.d 0 2) (by simp) with h4659 | h4659
                    · rcases p4638_3 (m.d 1 2) (by simp) with h4660 | h4660
                      · linarith only [h0, h4660, hlam]
                      · rcases p4638_3 (m.d 2 3) (by simp) with h4662 | h4662
                        · linarith only [h3, h4662, hlam]
                        · rcases p4638_3 (m.d 2 4) (by simp) with h4664 | h4664
                          · linarith only [h4, h4664, hlam]
                          · rcases p4638_3 (m.d 2 5) (by simp) with h4666 | h4666
                            · linarith only [h4666, hlam, p4638_0]
                            · rcases h3bigk with h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c | h4668c
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                rcases p4668_3 (m.d 0 3) (by simp) with h4670 | h4670
                                · rcases p4668_3 (m.d 1 3) (by simp) with h4671 | h4671
                                  · linarith only [h1, h4671, hlam]
                                  · rcases p4668_3 (m.d 2 3) (by simp) with h4673 | h4673
                                    · linarith only [h3, h4673, hlam]
                                    · linarith only [h3620, h4673, hlam]
                                · linarith only [h1, h4670, hlam]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                rcases p4668_3 (m.d 0 3) (by simp) with h4677 | h4677
                                · rcases p4668_3 (m.d 1 3) (by simp) with h4678 | h4678
                                  · linarith only [h1, h4678, hlam]
                                  · rcases p4668_3 (m.d 2 3) (by simp) with h4680 | h4680
                                    · linarith only [h3, h4680, hlam]
                                    · rcases p4668_3 (m.d 3 4) (by simp) with h4682 | h4682
                                      · linarith only [h4682, h6, hlam]
                                      · rcases p4668_3 (m.d 3 5) (by simp) with h4684 | h4684
                                        · linarith only [h4684, h7, hlam]
                                        · linarith only [h4632, h4684, hlam]
                                · linarith only [h3, h4677, hlam]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h3620, h4265, h4632, h7, hlam, p4668_2]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h0, h3, h3620, h4632, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h1, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h3620, hlam, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h0, h3, h3620, h4632, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4266, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h3, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4632, hc13, hc35, hlam, hphi, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h0, h3, h4632, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4632, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h6, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4265, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4631, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h4636, hlam, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h7, hlam, p4668_0]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h0, h3, h4265, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [h0, h3, h3620, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4668_1]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                rcases p4668_3 (m.d 0 3) (by simp) with h4708 | h4708
                                · rcases p4668_3 (m.d 1 3) (by simp) with h4709 | h4709
                                  · linarith only [h4266, h4709, hlam]
                                  · linarith only [h4265, h4709, hlam]
                                · linarith only [h4708, h6, hlam]
                              · have p4668_0 := h4668c.1
                                have p4668_1 := h4668c.2.1
                                have p4668_2 := h4668c.2.2.1
                                have p4668_3 := h4668c.2.2.2
                                linarith only [hlam, p4668_0]
                    · linarith only [h4659, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h0, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h3620, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h0, h3, h3620, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4206, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h3, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h0, h3, h4632, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h0, h3, h4631, h4632, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4632, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4631, hlam, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h4634, hlam, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h5, hlam, p4638_0]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    rcases p4638_3 (m.d 0 2) (by simp) with h4731 | h4731
                    · rcases p4638_3 (m.d 1 2) (by simp) with h4732 | h4732
                      · linarith only [h4732, hlam, p4638_0]
                      · rcases p4638_3 (m.d 2 3) (by simp) with h4734 | h4734
                        · linarith only [h4632, h4734, hlam]
                        · linarith only [h3620, h4734, hlam]
                    · linarith only [h0, h4731, hlam]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [h3620, hc12, hc25, hlam, hphi, p4638_1]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    rcases p4638_3 (m.d 0 2) (by simp) with h4739 | h4739
                    · rcases p4638_3 (m.d 1 2) (by simp) with h4740 | h4740
                      · linarith only [h4206, h4740, hlam]
                      · rcases p4638_3 (m.d 2 3) (by simp) with h4742 | h4742
                        · linarith only [h4632, h4742, hlam]
                        · linarith only [h4631, h4742, hlam]
                    · linarith only [h4, h4739, hlam]
                  · have p4638_0 := h4638c.1
                    have p4638_1 := h4638c.2.1
                    have p4638_2 := h4638c.2.2.1
                    have p4638_3 := h4638c.2.2.2
                    linarith only [hlam, p4638_0]
          · linarith only [h1, h3620, h4265, h4631, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h4748 | h4748
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4749 | h4749
        · linarith only [h4265, h4749, h6, h8, hlam]
        · linarith only [h4265, h4748, h4749, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h4752 | h4752
        · linarith only [h4752, h8, hc14, hlam, hphi, ht01, u0ehi3]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h4754 | h4754
          · rcases m.htr 2 3 5 (by decide) (by decide) with h4755 | h4755
            · rcases m.htr 2 4 5 (by decide) (by decide) with h4756 | h4756
              · linarith only [h4756, h8, hc24, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h4758 | h4758
                · linarith only [h4754, h4758, h8, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                · rcases h2bigk with h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c | h4760c
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h3, h3620, h4265, h4755, h4758, hlam, p4760_2]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h0, h3620, h4265, h4755, h4758, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    rcases p4760_3 (m.d 0 2) (by simp) with h4764 | h4764
                    · rcases p4760_3 (m.d 1 2) (by simp) with h4765 | h4765
                      · linarith only [h0, h4765, hlam]
                      · rcases p4760_3 (m.d 2 3) (by simp) with h4767 | h4767
                        · linarith only [h3, h4767, hlam]
                        · linarith only [h4754, h4767, hlam]
                    · linarith only [h4764, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    rcases p4760_3 (m.d 0 2) (by simp) with h4771 | h4771
                    · rcases p4760_3 (m.d 1 2) (by simp) with h4772 | h4772
                      · linarith only [h0, h4772, hlam]
                      · rcases p4760_3 (m.d 2 3) (by simp) with h4774 | h4774
                        · linarith only [h3, h4774, hlam]
                        · linarith only [h4755, h4774, hlam]
                    · linarith only [h4771, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h0, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h3620, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h3620, h4265, h4755, h4758, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4206, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h3, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    rcases p4760_3 (m.d 0 2) (by simp) with h4784 | h4784
                    · rcases p4760_3 (m.d 1 2) (by simp) with h4785 | h4785
                      · linarith only [h4785, hlam, p4760_0]
                      · rcases p4760_3 (m.d 2 3) (by simp) with h4787 | h4787
                        · rcases p4760_3 (m.d 2 4) (by simp) with h4788 | h4788
                          · linarith only [h4754, h4788, hlam]
                          · linarith only [h3620, h4265, h4754, h4788, hlam]
                        · linarith only [h4787, hlam, p4760_0]
                    · linarith only [h0, h4784, hlam]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h0, h3, h3620, h4265, h4754, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h0, h3, h4206, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4754, hlam, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4756, hlam, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h5, hlam, p4760_0]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    rcases p4760_3 (m.d 0 2) (by simp) with h4802 | h4802
                    · rcases p4760_3 (m.d 1 2) (by simp) with h4803 | h4803
                      · linarith only [h4803, hlam, p4760_0]
                      · rcases p4760_3 (m.d 2 3) (by simp) with h4805 | h4805
                        · rcases p4760_3 (m.d 2 4) (by simp) with h4806 | h4806
                          · linarith only [h4756, h4806, hlam]
                          · linarith only [h3620, h4265, h4754, h4806, hlam]
                        · linarith only [h3620, h4805, hlam]
                    · linarith only [h0, h4802, hlam]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h4755, hlam, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [h3620, h4265, h4754, hc12, hc25, hlam, hphi, p4760_1]
                  · have p4760_0 := h4760c.1
                    have p4760_1 := h4760c.2.1
                    have p4760_2 := h4760c.2.2.1
                    have p4760_3 := h4760c.2.2.2
                    linarith only [hlam, p4760_0]
            · linarith only [h3620, h4265, h4754, h4755, hc12, hc35, hlam, hphi, ht23]
          · linarith only [h3620, h4754, h6, h8, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9616000 in
set_option maxHeartbeats 9616000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 2 3 (by decide) (by decide) with h3620 | h3620
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h3620
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8 h3620

set_option maxHeartbeats 9616000 in
set_option maxHeartbeats 9616000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8
  · exact r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s7_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 h8

end R2N4
