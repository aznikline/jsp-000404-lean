import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9090000 in
set_option maxHeartbeats 9090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s7 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s8 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h4227 | h4227
    · linarith only [h4227, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h4229 | h4229
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4230 | h4230
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4231 | h4231
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4232 | h4232
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4233 | h4233
              · linarith only [h1, h4233, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4235 | h4235
                · linarith only [h2, h4227, h4235, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4237 | h4237
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4238 | h4238
                    · linarith only [h0, h4229, h4238, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4240 | h4240
                      · linarith only [h2, h4227, h4230, h4240, h7, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4242 | h4242
                        · linarith only [h1, h2, h4227, h4229, h4230, h4237, h4242, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h0bigk with h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c | h4244c
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h0, h4231, h4237, h4238, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4247 | h4247
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4248 | h4248
                              · linarith only [h0, h4248, hlam]
                              · linarith only [h4, h4248, hlam]
                            · linarith only [h1, h4247, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4252 | h4252
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4253 | h4253
                              · linarith only [h0, h4253, hlam]
                              · linarith only [h4253, h5, hlam]
                            · linarith only [h2, h4252, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4257 | h4257
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4258 | h4258
                              · linarith only [h0, h4258, hlam]
                              · linarith only [h4258, h6, hlam]
                            · linarith only [h3, h4257, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h0, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4264 | h4264
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4265 | h4265
                              · rcases p4244_3 (m.d 0 3) (by simp) with h4266 | h4266
                                · linarith only [h4, h4266, hlam]
                                · rcases p4244_3 (m.d 0 4) (by simp) with h4268 | h4268
                                  · linarith only [h4268, h5, hlam]
                                  · rcases p4244_3 (m.d 0 5) (by simp) with h4270 | h4270
                                    · linarith only [h4270, h6, hlam]
                                    · linarith only [h4270, h8, hlam]
                              · linarith only [h4, h4265, hlam]
                            · linarith only [h1, h4264, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4275 | h4275
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4276 | h4276
                              · rcases p4244_3 (m.d 0 3) (by simp) with h4277 | h4277
                                · linarith only [h4, h4277, hlam]
                                · linarith only [h4277, h7, hlam]
                              · linarith only [h4276, h5, hlam]
                            · linarith only [h2, h4275, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4282 | h4282
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4283 | h4283
                              · rcases p4244_3 (m.d 0 3) (by simp) with h4284 | h4284
                                · linarith only [h4, h4284, hlam]
                                · rcases p4244_3 (m.d 0 4) (by simp) with h4286 | h4286
                                  · linarith only [h4286, h5, hlam]
                                  · rcases p4244_3 (m.d 0 5) (by simp) with h4288 | h4288
                                    · linarith only [h4288, h6, hlam]
                                    · rcases h2bigk with h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c | h4290c
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h4231, h4237, h4238, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        rcases p4290_3 (m.d 0 2) (by simp) with h4293 | h4293
                                        · rcases p4290_3 (m.d 1 2) (by simp) with h4294 | h4294
                                          · linarith only [h0, h4294, hlam]
                                          · linarith only [h4229, h4294, hlam]
                                        · linarith only [h4293, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        rcases p4290_3 (m.d 0 2) (by simp) with h4298 | h4298
                                        · rcases p4290_3 (m.d 1 2) (by simp) with h4299 | h4299
                                          · linarith only [h0, h4299, hlam]
                                          · linarith only [h4230, h4299, hlam]
                                        · linarith only [h4298, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        rcases p4290_3 (m.d 0 2) (by simp) with h4303 | h4303
                                        · rcases p4290_3 (m.d 1 2) (by simp) with h4304 | h4304
                                          · linarith only [h0, h4304, hlam]
                                          · linarith only [h4231, h4304, hlam]
                                        · linarith only [h4303, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h4237, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        rcases p4290_3 (m.d 0 2) (by simp) with h4311 | h4311
                                        · rcases p4290_3 (m.d 1 2) (by simp) with h4312 | h4312
                                          · rcases p4290_3 (m.d 2 3) (by simp) with h4313 | h4313
                                            · linarith only [h4229, h4313, hlam]
                                            · linarith only [h4237, h4313, hlam]
                                          · linarith only [h4312, hlam, p4290_0]
                                        · linarith only [h4311, h5, hlam]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h4237, h4238, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4229, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h4238, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4244_1, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4238, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h5, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4230, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4237, hlam, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4240, hlam, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h6, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h4231, hlam, p4290_0]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4244_1, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [h0, h3, h4231, h4237, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4244_1, p4290_1]
                                      · have p4290_0 := h4290c.1
                                        have p4290_1 := h4290c.2.1
                                        have p4290_2 := h4290c.2.2.1
                                        have p4290_3 := h4290c.2.2.2
                                        linarith only [hlam, p4290_0]
                              · linarith only [h4283, h6, hlam]
                            · linarith only [h3, h4282, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h1, hlam, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h4, hlam, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h2, h4230, h4237, h4242, h8, hc34, hc45, hlam, hphi, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h8, hlam, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h2, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h5, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h7, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h4227, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h3, hlam, p4244_0]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h6, hlam, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [h1, h4229, h4237, h4242, h8, hc34, hc45, hlam, hphi, p4244_1]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            rcases p4244_3 (m.d 0 1) (by simp) with h4349 | h4349
                            · rcases p4244_3 (m.d 0 2) (by simp) with h4350 | h4350
                              · rcases p4244_3 (m.d 0 3) (by simp) with h4351 | h4351
                                · linarith only [h4351, h8, hlam]
                                · linarith only [h4351, h7, hlam]
                              · linarith only [h4350, h5, hlam]
                            · linarith only [h2, h4349, hlam]
                          · have p4244_0 := h4244c.1
                            have p4244_1 := h4244c.2.1
                            have p4244_2 := h4244c.2.2.1
                            have p4244_3 := h4244c.2.2.2
                            linarith only [hlam, p4244_0]
                  · linarith only [h4237, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h4232, h7, h8, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4359 | h4359
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4360 | h4360
              · linarith only [h1, h4360, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4362 | h4362
                · linarith only [h2, h4227, h4362, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4364 | h4364
                  · linarith only [h0, h4229, h4231, h4364, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h1, h4359, h4364, h8, hc23, hc35, hlam, hphi]
            · linarith only [h4359, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h4227, h4229, h4230, h5, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h4369 | h4369
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4370 | h4370
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4371 | h4371
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4372 | h4372
              · linarith only [h4, h4229, h4369, h4372, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h4229, h4370, h4372, hlam]
            · linarith only [h4229, h4369, h4371, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4376 | h4376
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4377 | h4377
              · linarith only [h1, h4377, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4379 | h4379
                · linarith only [h4, h4227, h4229, h4369, h4379, h8, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4381 | h4381
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4382 | h4382
                    · linarith only [h4, h4382, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4384 | h4384
                      · linarith only [h4, h4227, h4229, h4369, h4384, h8, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4386 | h4386
                        · linarith only [h4, h4227, h4229, h4369, h4381, h4386, h8, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h4, h4229, h4369, h4386, h8, hc24, hc45, hlam, hphi]
                  · linarith only [h4229, h4369, h4381, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h4229, h4369, h4376, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4391 | h4391
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4392 | h4392
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4393 | h4393
              · linarith only [h1, h4393, h8, hlam]
              · linarith only [h4229, h4391, h4393, hlam]
            · linarith only [h4229, h4391, h4392, h7, h8, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h4397 | h4397
            · rcases m.htr 1 3 5 (by decide) (by decide) with h4398 | h4398
              · linarith only [h1, h4398, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h4400 | h4400
                · linarith only [h2, h4227, h4369, h4400, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h4402 | h4402
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h4403 | h4403
                    · linarith only [h4, h4403, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h4405 | h4405
                      · linarith only [h4227, h4405, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h4407 | h4407
                        · linarith only [h4227, h4369, h4397, h4407, h5, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · rcases h0bigk with h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c | h4409c
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h4, h4229, h4397, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4412 | h4412
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4413 | h4413
                              · linarith only [h0, h4413, hlam]
                              · linarith only [h4, h4413, hlam]
                            · linarith only [h1, h4412, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4417 | h4417
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4418 | h4418
                              · linarith only [h0, h4418, hlam]
                              · linarith only [h4418, h5, hlam]
                            · linarith only [h2, h4417, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4422 | h4422
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4423 | h4423
                              · linarith only [h0, h4423, hlam]
                              · linarith only [h4423, h6, hlam]
                            · linarith only [h3, h4422, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h0, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4429 | h4429
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4430 | h4430
                              · rcases p4409_3 (m.d 0 3) (by simp) with h4431 | h4431
                                · linarith only [h4, h4431, hlam]
                                · rcases p4409_3 (m.d 0 4) (by simp) with h4433 | h4433
                                  · linarith only [h4433, h5, hlam]
                                  · rcases p4409_3 (m.d 0 5) (by simp) with h4435 | h4435
                                    · linarith only [h4435, h6, hlam]
                                    · linarith only [h4435, h8, hlam]
                              · linarith only [h4, h4430, hlam]
                            · linarith only [h1, h4429, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4440 | h4440
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4441 | h4441
                              · rcases p4409_3 (m.d 0 3) (by simp) with h4442 | h4442
                                · linarith only [h4, h4442, hlam]
                                · linarith only [h4442, h7, hlam]
                              · linarith only [h4441, h5, hlam]
                            · linarith only [h2, h4440, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            rcases p4409_3 (m.d 0 1) (by simp) with h4447 | h4447
                            · rcases p4409_3 (m.d 0 2) (by simp) with h4448 | h4448
                              · rcases p4409_3 (m.d 0 3) (by simp) with h4449 | h4449
                                · linarith only [h4, h4449, hlam]
                                · rcases p4409_3 (m.d 0 4) (by simp) with h4451 | h4451
                                  · linarith only [h4451, h5, hlam]
                                  · rcases p4409_3 (m.d 0 5) (by simp) with h4453 | h4453
                                    · linarith only [h4453, h6, hlam]
                                    · rcases h2bigk with h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c | h4455c
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4369, h5, h7, h8, hlam, p4409_1, p4455_2]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        rcases p4455_3 (m.d 0 2) (by simp) with h4458 | h4458
                                        · rcases p4455_3 (m.d 1 2) (by simp) with h4459 | h4459
                                          · linarith only [h0, h4459, hlam]
                                          · rcases p4455_3 (m.d 2 3) (by simp) with h4461 | h4461
                                            · linarith only [h4461, hlam, p4455_0]
                                            · rcases p4455_3 (m.d 2 4) (by simp) with h4463 | h4463
                                              · linarith only [h4463, h5, hlam]
                                              · rcases p4455_3 (m.d 2 5) (by simp) with h4465 | h4465
                                                · linarith only [h4465, h6, hlam]
                                                · linarith only [h4403, h4465, hlam]
                                        · linarith only [h4458, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        rcases p4455_3 (m.d 0 2) (by simp) with h4469 | h4469
                                        · rcases p4455_3 (m.d 1 2) (by simp) with h4470 | h4470
                                          · linarith only [h0, h4470, hlam]
                                          · rcases p4455_3 (m.d 2 3) (by simp) with h4472 | h4472
                                            · linarith only [h4, h4472, hlam]
                                            · linarith only [h4402, h4472, hlam]
                                        · linarith only [h4469, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        rcases p4455_3 (m.d 0 2) (by simp) with h4476 | h4476
                                        · rcases p4455_3 (m.d 1 2) (by simp) with h4477 | h4477
                                          · linarith only [h0, h4477, hlam]
                                          · rcases p4455_3 (m.d 2 3) (by simp) with h4479 | h4479
                                            · linarith only [h4, h4479, hlam]
                                            · rcases p4455_3 (m.d 2 4) (by simp) with h4481 | h4481
                                              · linarith only [h4481, h5, hlam]
                                              · rcases p4455_3 (m.d 2 5) (by simp) with h4483 | h4483
                                                · linarith only [h4483, hlam, p4455_0]
                                                · rcases h3bigk with h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c | h4485c
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4397, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h0, h4369, h4402, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h8, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h1, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4229, hlam, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h0, h1, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4398, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h0, h4, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h0, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4409_1, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4403, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h7, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4397, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4402, hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [hlam, p4485_0]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4407, hlam, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h1, h4397, h4407, hc34, hc45, hlam, hphi, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4397, h4407, hc34, hc45, hlam, hphi, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [h4229, h4407, hc12, hc45, hlam, hphi, ht23, ht34, p4485_1]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    rcases p4485_3 (m.d 0 3) (by simp) with h4509 | h4509
                                                    · linarith only [h4509, h8, hlam]
                                                    · linarith only [h4509, h7, hlam]
                                                  · have p4485_0 := h4485c.1
                                                    have p4485_1 := h4485c.2.1
                                                    have p4485_2 := h4485c.2.2.1
                                                    have p4485_3 := h4485c.2.2.2
                                                    linarith only [hlam, p4485_0]
                                        · linarith only [h4476, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4229, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4369, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4391, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4, h4407, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, h4, h4369, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4409_1, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4403, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h5, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4409_1, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4402, hlam, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h4405, hlam, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h6, hlam, p4455_0]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4409_1, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4409_1, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [h0, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p4409_1, p4455_1]
                                      · have p4455_0 := h4455c.1
                                        have p4455_1 := h4455c.2.1
                                        have p4455_2 := h4455c.2.2.1
                                        have p4455_3 := h4455c.2.2.2
                                        linarith only [hlam, p4455_0]
                              · linarith only [h4448, h6, hlam]
                            · linarith only [h3, h4447, hlam]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h1, hlam, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h4, hlam, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h2, h4407, h8, hc14, hc45, hlam, hphi, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h8, hlam, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h2, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h5, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h7, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h4227, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h3, hlam, p4409_0]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h6, hlam, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h1, h4397, h4407, h8, hc34, hc45, hlam, hphi, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [h4369, h4407, h5, h8, hc12, hc45, hlam, hphi, ht23, ht34, p4409_1]
                          · have p4409_0 := h4409c.1
                            have p4409_1 := h4409c.2.1
                            have p4409_2 := h4409c.2.2.1
                            have p4409_3 := h4409c.2.2.2
                            linarith only [hlam, p4409_0]
                  · linarith only [h1, h4229, h4397, h4402, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h4397, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 4 5 (by decide) (by decide) with h4554 | h4554
  · rcases m.htr 1 2 3 (by decide) (by decide) with h4555 | h4555
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4556 | h4556
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4557 | h4557
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4558 | h4558
          · linarith only [h1, h4553, h4558, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4560 | h4560
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4561 | h4561
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4562 | h4562
                · linarith only [h1, h4555, h4560, h4562, h7, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4564 | h4564
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4565 | h4565
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4566 | h4566
                      · rcases h0bigk with h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c | h4567c
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h4, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4570 | h4570
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4571 | h4571
                            · linarith only [h0, h4571, hlam]
                            · linarith only [h4, h4571, hlam]
                          · linarith only [h1, h4570, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4575 | h4575
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4576 | h4576
                            · linarith only [h0, h4576, hlam]
                            · linarith only [h4576, h5, hlam]
                          · linarith only [h2, h4575, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4580 | h4580
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4581 | h4581
                            · linarith only [h0, h4581, hlam]
                            · linarith only [h4581, h6, hlam]
                          · linarith only [h3, h4580, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h0, hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4587 | h4587
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4588 | h4588
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4589 | h4589
                              · linarith only [h4, h4589, hlam]
                              · rcases p4567_3 (m.d 0 4) (by simp) with h4591 | h4591
                                · linarith only [h4591, h5, hlam]
                                · linarith only [h4591, h7, hlam]
                            · linarith only [h4, h4588, hlam]
                          · linarith only [h1, h4587, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4596 | h4596
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4597 | h4597
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4598 | h4598
                              · linarith only [h4, h4598, hlam]
                              · rcases p4567_3 (m.d 0 4) (by simp) with h4600 | h4600
                                · linarith only [h4600, h5, hlam]
                                · rcases p4567_3 (m.d 0 5) (by simp) with h4602 | h4602
                                  · linarith only [h4602, h6, hlam]
                                  · rcases h2bigk with h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c | h4604c
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4556, h4562, h4564, h4566, hc02, hc45, hlam, hphi, ht0b, ht5b, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      rcases p4604_3 (m.d 0 2) (by simp) with h4607 | h4607
                                      · rcases p4604_3 (m.d 1 2) (by simp) with h4608 | h4608
                                        · linarith only [h0, h4608, hlam]
                                        · linarith only [h4555, h4608, hlam]
                                      · linarith only [h4607, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      rcases p4604_3 (m.d 0 2) (by simp) with h4612 | h4612
                                      · rcases p4604_3 (m.d 1 2) (by simp) with h4613 | h4613
                                        · linarith only [h0, h4613, hlam]
                                        · linarith only [h4556, h4613, hlam]
                                      · linarith only [h4612, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      rcases p4604_3 (m.d 0 2) (by simp) with h4617 | h4617
                                      · rcases p4604_3 (m.d 1 2) (by simp) with h4618 | h4618
                                        · linarith only [h0, h4618, hlam]
                                        · linarith only [h4557, h4618, hlam]
                                      · linarith only [h4617, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, h4562, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      rcases p4604_3 (m.d 0 2) (by simp) with h4626 | h4626
                                      · rcases p4604_3 (m.d 1 2) (by simp) with h4627 | h4627
                                        · rcases p4604_3 (m.d 2 3) (by simp) with h4628 | h4628
                                          · linarith only [h4555, h4628, hlam]
                                          · linarith only [h4564, h4628, hlam]
                                        · linarith only [h4627, hlam, p4604_0]
                                      · linarith only [h4626, h6, hlam]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4555, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4562, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, h1, h4555, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p4567_1, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h5, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4556, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, h4564, h5, hc01, hc35, hlam, hphi, ht0b, ht5b, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h0, h2, h4556, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4567_1, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h6, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4557, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4564, hlam, p4604_1]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [h4565, hlam, p4604_0]
                                    · have p4604_0 := h4604c.1
                                      have p4604_1 := h4604c.2.1
                                      have p4604_2 := h4604c.2.2.1
                                      have p4604_3 := h4604c.2.2.2
                                      linarith only [hlam, p4604_0]
                            · linarith only [h4597, h5, hlam]
                          · linarith only [h2, h4596, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4650 | h4650
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4651 | h4651
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4652 | h4652
                              · linarith only [h4, h4652, hlam]
                              · linarith only [h4553, h4652, hlam]
                            · linarith only [h4651, h6, hlam]
                          · linarith only [h3, h4650, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h1, hlam, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h4, hlam, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h7, hlam, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4661 | h4661
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4662 | h4662
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4663 | h4663
                              · rcases p4567_3 (m.d 0 4) (by simp) with h4664 | h4664
                                · rcases p4567_3 (m.d 0 5) (by simp) with h4665 | h4665
                                  · linarith only [h4553, h4665, hlam]
                                  · rcases h2bigk with h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c | h4667c
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h4555, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      rcases p4667_3 (m.d 0 2) (by simp) with h4670 | h4670
                                      · rcases p4667_3 (m.d 1 2) (by simp) with h4671 | h4671
                                        · linarith only [h0, h4671, hlam]
                                        · linarith only [h4555, h4671, hlam]
                                      · linarith only [h4670, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      rcases p4667_3 (m.d 0 2) (by simp) with h4675 | h4675
                                      · rcases p4667_3 (m.d 1 2) (by simp) with h4676 | h4676
                                        · linarith only [h0, h4676, hlam]
                                        · linarith only [h4556, h4676, hlam]
                                      · linarith only [h4675, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      rcases p4667_3 (m.d 0 2) (by simp) with h4680 | h4680
                                      · rcases p4667_3 (m.d 1 2) (by simp) with h4681 | h4681
                                        · linarith only [h0, h4681, hlam]
                                        · linarith only [h4557, h4681, hlam]
                                      · linarith only [h4680, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h4562, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      rcases p4667_3 (m.d 0 2) (by simp) with h4689 | h4689
                                      · rcases p4667_3 (m.d 1 2) (by simp) with h4690 | h4690
                                        · rcases p4667_3 (m.d 2 3) (by simp) with h4691 | h4691
                                          · linarith only [h4555, h4691, hlam]
                                          · linarith only [h4564, h4691, hlam]
                                        · linarith only [h4690, hlam, p4667_0]
                                      · linarith only [h4689, h6, hlam]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4555, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4562, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h4555, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h5, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4556, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h3, h4556, h4557, h4564, h4566, h7, hc01, hc23, hc34, hc45, hlam, hphi, ht0b, ht5b, p4567_1, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h0, h4556, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h6, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4557, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4564, hlam, p4667_1]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [h4565, hlam, p4667_0]
                                    · have p4667_0 := h4667c.1
                                      have p4667_1 := h4667c.2.1
                                      have p4667_2 := h4667c.2.2.1
                                      have p4667_3 := h4667c.2.2.2
                                      linarith only [hlam, p4667_0]
                                · linarith only [h4554, h4664, hlam]
                              · linarith only [h4553, h4663, hlam]
                            · linarith only [h4662, h6, hlam]
                          · linarith only [h3, h4661, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h2, hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h5, hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4717 | h4717
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4718 | h4718
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4719 | h4719
                              · linarith only [h4719, h7, hlam]
                              · rcases p4567_3 (m.d 0 4) (by simp) with h4721 | h4721
                                · rcases p4567_3 (m.d 0 5) (by simp) with h4722 | h4722
                                  · linarith only [h4554, h4722, hlam]
                                  · rcases h2bigk with h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c | h4724c
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, h4555, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      rcases p4724_3 (m.d 0 2) (by simp) with h4727 | h4727
                                      · rcases p4724_3 (m.d 1 2) (by simp) with h4728 | h4728
                                        · linarith only [h0, h4728, hlam]
                                        · linarith only [h4555, h4728, hlam]
                                      · linarith only [h4727, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      rcases p4724_3 (m.d 0 2) (by simp) with h4732 | h4732
                                      · rcases p4724_3 (m.d 1 2) (by simp) with h4733 | h4733
                                        · linarith only [h0, h4733, hlam]
                                        · linarith only [h4556, h4733, hlam]
                                      · linarith only [h4732, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      rcases p4724_3 (m.d 0 2) (by simp) with h4737 | h4737
                                      · rcases p4724_3 (m.d 1 2) (by simp) with h4738 | h4738
                                        · linarith only [h0, h4738, hlam]
                                        · linarith only [h4557, h4738, hlam]
                                      · linarith only [h4737, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, h4562, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      rcases p4724_3 (m.d 0 2) (by simp) with h4746 | h4746
                                      · rcases p4724_3 (m.d 1 2) (by simp) with h4747 | h4747
                                        · rcases p4724_3 (m.d 2 3) (by simp) with h4748 | h4748
                                          · linarith only [h4555, h4748, hlam]
                                          · linarith only [h4564, h4748, hlam]
                                        · linarith only [h4747, hlam, p4724_0]
                                      · linarith only [h4746, h6, hlam]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4555, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4562, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h1, h4555, h5, hc02, hc25, hlam, hphi, ht0b, ht5b, p4567_1, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h5, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4556, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, h4556, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h0, h4556, h4564, h4566, hc01, hc45, hlam, hphi, ht0b, ht5b, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h6, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4557, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4564, hlam, p4724_1]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [h4565, hlam, p4724_0]
                                    · have p4724_0 := h4724c.1
                                      have p4724_1 := h4724c.2.1
                                      have p4724_2 := h4724c.2.2.1
                                      have p4724_3 := h4724c.2.2.2
                                      linarith only [hlam, p4724_0]
                                · linarith only [h4721, h7, hlam]
                            · linarith only [h4, h4718, hlam]
                          · linarith only [h1, h4717, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          rcases p4567_3 (m.d 0 1) (by simp) with h4772 | h4772
                          · rcases p4567_3 (m.d 0 2) (by simp) with h4773 | h4773
                            · rcases p4567_3 (m.d 0 3) (by simp) with h4774 | h4774
                              · linarith only [h4774, h7, hlam]
                              · linarith only [h4553, h4774, hlam]
                            · linarith only [h4773, h6, hlam]
                          · linarith only [h3, h4772, hlam]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h3, hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h6, hlam, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h4553, hlam, p4567_0]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [h4554, hlam, p4567_1]
                        · have p4567_0 := h4567c.1
                          have p4567_1 := h4567c.2.1
                          have p4567_2 := h4567c.2.2.1
                          have p4567_3 := h4567c.2.2.2
                          linarith only [hlam, p4567_0]
                      · linarith only [h4554, h4566, h7, hlam]
                    · linarith only [h0, h4556, h4561, h4562, h4564, h4565, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h4553, h4564, h7, hc23, hc34, hlam, hphi]
              · linarith only [h4558, h4560, h4561, hlam]
            · linarith only [h4553, h4560, h7, hc13, hc34, hlam, hphi]
        · linarith only [h4553, h4555, h4557, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4790 | h4790
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4791 | h4791
          · linarith only [h1, h4553, h4791, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4793 | h4793
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4794 | h4794
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4795 | h4795
                · linarith only [h4555, h4556, h4795, h5, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4797 | h4797
                  · linarith only [h0, h4555, h4556, h4797, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h4793, h4797, h7, hc23, hc34, hlam, hphi]
              · linarith only [h4553, h4554, h4555, h4556, h4794, h7, hc23, hc34, hlam, hphi]
            · linarith only [h4553, h4793, h7, hc13, hc34, hlam, hphi]
        · linarith only [h4553, h4555, h4790, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h4803 | h4803
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4804 | h4804
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4805 | h4805
          · linarith only [h4, h4555, h4803, h4805, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h4555, h4803, h4805, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4808 | h4808
          · linarith only [h4553, h4803, h4804, h4808, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h4555, h4803, h4808, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h4811 | h4811
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4812 | h4812
          · linarith only [h1, h4553, h4812, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4814 | h4814
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4815 | h4815
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4816 | h4816
                · linarith only [h4, h4816, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4818 | h4818
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4819 | h4819
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4820 | h4820
                      · rcases h0bigk with h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c | h4821c
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4, h4555, h4811, h4818, h4820, hc01, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4, h4555, h4811, h4818, h4820, hc01, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4, h4555, h4811, h4818, h4820, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          rcases p4821_3 (m.d 0 1) (by simp) with h4826 | h4826
                          · rcases p4821_3 (m.d 0 2) (by simp) with h4827 | h4827
                            · linarith only [h0, h4827, hlam]
                            · linarith only [h4827, h6, hlam]
                          · linarith only [h3, h4826, hlam]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h0, hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4, h4555, h4811, h4818, h4820, hc02, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h0, h4, h4555, h4811, h4818, h4820, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          rcases p4821_3 (m.d 0 1) (by simp) with h4835 | h4835
                          · rcases p4821_3 (m.d 0 2) (by simp) with h4836 | h4836
                            · rcases p4821_3 (m.d 0 3) (by simp) with h4837 | h4837
                              · linarith only [h4, h4837, hlam]
                              · linarith only [h4553, h4837, hlam]
                            · linarith only [h4836, h6, hlam]
                          · linarith only [h3, h4835, hlam]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h1, hlam, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4, hlam, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h7, hlam, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          rcases p4821_3 (m.d 0 1) (by simp) with h4846 | h4846
                          · rcases p4821_3 (m.d 0 2) (by simp) with h4847 | h4847
                            · rcases p4821_3 (m.d 0 3) (by simp) with h4848 | h4848
                              · rcases p4821_3 (m.d 0 4) (by simp) with h4849 | h4849
                                · rcases p4821_3 (m.d 0 5) (by simp) with h4850 | h4850
                                  · linarith only [h4553, h4850, hlam]
                                  · rcases h2bigk with h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c | h4852c
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      rcases p4852_3 (m.d 0 2) (by simp) with h4854 | h4854
                                      · rcases p4852_3 (m.d 1 2) (by simp) with h4855 | h4855
                                        · linarith only [h0, h4855, hlam]
                                        · rcases p4852_3 (m.d 2 3) (by simp) with h4857 | h4857
                                          · linarith only [h4, h4857, hlam]
                                          · linarith only [h4555, h4857, hlam]
                                      · linarith only [h0, h4854, hlam]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h0, h4555, h4811, h4818, h4820, hc01, hc45, hlam, hphi, ht0b, ht5b, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h0, h4555, h4811, h4816, h4818, h4820, hc01, hc45, hlam, hphi, ht0b, ht5b, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4, h4555, h4811, hlam, p4852_2]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h0, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4555, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4803, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4, h4555, h4818, h4820, hc02, hc45, hlam, hphi, ht0b, ht5b, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4, h7, hc12, hc34, hlam, hphi, ht23, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4816, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      rcases p4852_3 (m.d 0 2) (by simp) with h4873 | h4873
                                      · rcases p4852_3 (m.d 1 2) (by simp) with h4874 | h4874
                                        · linarith only [h4555, h4874, hlam]
                                        · linarith only [h4811, h4874, hlam]
                                      · linarith only [h4873, h6, hlam]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h5, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h0, h4811, h4818, h4820, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h0, h4555, h4811, h4818, h4820, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      rcases p4852_3 (m.d 0 2) (by simp) with h4882 | h4882
                                      · rcases p4852_3 (m.d 1 2) (by simp) with h4883 | h4883
                                        · linarith only [h4803, h4883, hlam]
                                        · linarith only [h4811, h4883, hlam]
                                      · linarith only [h4882, h6, hlam]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h6, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4811, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4818, hlam, p4852_1]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [h4819, hlam, p4852_0]
                                    · have p4852_0 := h4852c.1
                                      have p4852_1 := h4852c.2.1
                                      have p4852_2 := h4852c.2.2.1
                                      have p4852_3 := h4852c.2.2.2
                                      linarith only [hlam, p4852_0]
                                · linarith only [h4554, h4849, hlam]
                              · linarith only [h4553, h4848, hlam]
                            · linarith only [h4847, h6, hlam]
                          · linarith only [h3, h4846, hlam]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h2, hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h5, hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h2, h4, h4555, h4811, h4818, h4820, hc01, hc45, hlam, hphi, ht0b, ht5b, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          rcases p4821_3 (m.d 0 1) (by simp) with h4900 | h4900
                          · rcases p4821_3 (m.d 0 2) (by simp) with h4901 | h4901
                            · rcases p4821_3 (m.d 0 3) (by simp) with h4902 | h4902
                              · linarith only [h4902, h7, hlam]
                              · linarith only [h4553, h4902, hlam]
                            · linarith only [h4901, h6, hlam]
                          · linarith only [h3, h4900, hlam]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h3, hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h6, hlam, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4553, hlam, p4821_0]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [h4554, hlam, p4821_1]
                        · have p4821_0 := h4821c.1
                          have p4821_1 := h4821c.2.1
                          have p4821_2 := h4821c.2.2.1
                          have p4821_3 := h4821c.2.2.2
                          linarith only [hlam, p4821_0]
                      · linarith only [h4, h4555, h4811, h4818, h4820, h7, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                    · linarith only [h4553, h4554, h4803, h4811, h4818, h4819, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h4553, h4555, h4811, h4818, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h4555, h4811, h4812, h4815, hlam]
            · linarith only [h4553, h4555, h4814, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h4917 | h4917
          · linarith only [h1, h4553, h4917, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h4919 | h4919
            · rcases m.htr 1 4 5 (by decide) (by decide) with h4920 | h4920
              · rcases m.htr 2 3 4 (by decide) (by decide) with h4921 | h4921
                · linarith only [h4, h4921, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h4923 | h4923
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h4924 | h4924
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h4925 | h4925
                      · rcases h0bigk with h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c | h4926c
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4, h4555, h4919, hc01, hc35, hlam, hphi, ht0b, ht5b, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h4929 | h4929
                          · rcases p4926_3 (m.d 0 2) (by simp) with h4930 | h4930
                            · linarith only [h0, h4930, hlam]
                            · linarith only [h4, h4930, hlam]
                          · linarith only [h1, h4929, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h4934 | h4934
                          · rcases p4926_3 (m.d 0 2) (by simp) with h4935 | h4935
                            · linarith only [h0, h4935, hlam]
                            · linarith only [h4935, h5, hlam]
                          · linarith only [h2, h4934, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h4939 | h4939
                          · rcases p4926_3 (m.d 0 2) (by simp) with h4940 | h4940
                            · linarith only [h0, h4940, hlam]
                            · linarith only [h4940, h6, hlam]
                          · linarith only [h3, h4939, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h0, hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h4946 | h4946
                          · rcases p4926_3 (m.d 0 2) (by simp) with h4947 | h4947
                            · rcases p4926_3 (m.d 0 3) (by simp) with h4948 | h4948
                              · linarith only [h4, h4948, hlam]
                              · rcases p4926_3 (m.d 0 4) (by simp) with h4950 | h4950
                                · linarith only [h4950, h5, hlam]
                                · linarith only [h4950, h7, hlam]
                            · linarith only [h4, h4947, hlam]
                          · linarith only [h1, h4946, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h4955 | h4955
                          · rcases p4926_3 (m.d 0 2) (by simp) with h4956 | h4956
                            · rcases p4926_3 (m.d 0 3) (by simp) with h4957 | h4957
                              · linarith only [h4, h4957, hlam]
                              · rcases p4926_3 (m.d 0 4) (by simp) with h4959 | h4959
                                · linarith only [h4959, h5, hlam]
                                · rcases p4926_3 (m.d 0 5) (by simp) with h4961 | h4961
                                  · linarith only [h4961, h6, hlam]
                                  · rcases h2bigk with h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c | h4963c
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4811, h4921, h4923, h5, hlam, p4926_1, p4963_2]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      rcases p4963_3 (m.d 0 2) (by simp) with h4966 | h4966
                                      · rcases p4963_3 (m.d 1 2) (by simp) with h4967 | h4967
                                        · linarith only [h0, h4967, hlam]
                                        · rcases p4963_3 (m.d 2 3) (by simp) with h4969 | h4969
                                          · linarith only [h4969, hlam, p4963_0]
                                          · rcases p4963_3 (m.d 2 4) (by simp) with h4971 | h4971
                                            · linarith only [h4971, h5, hlam]
                                            · linarith only [h4921, h4971, hlam]
                                      · linarith only [h4966, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      rcases p4963_3 (m.d 0 2) (by simp) with h4975 | h4975
                                      · rcases p4963_3 (m.d 1 2) (by simp) with h4976 | h4976
                                        · linarith only [h0, h4976, hlam]
                                        · rcases p4963_3 (m.d 2 3) (by simp) with h4978 | h4978
                                          · linarith only [h4, h4978, hlam]
                                          · rcases p4963_3 (m.d 2 4) (by simp) with h4980 | h4980
                                            · linarith only [h4980, hlam, p4963_0]
                                            · rcases p4963_3 (m.d 2 5) (by simp) with h4982 | h4982
                                              · linarith only [h4982, h6, hlam]
                                              · rcases h3bigk with h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c | h4984c
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h7, hc13, hc34, hlam, hphi, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4811, h4923, h7, hc12, hc34, hlam, hphi, ht23, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h7, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h0, h4925, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4926_1, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h1, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4555, hlam, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4917, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h0, h1, h4925, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p4926_1, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h0, h4921, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4926_1, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4921, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h0, h4921, h4925, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p4926_1, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4, h4811, h4923, hc12, hc34, hlam, hphi, ht23, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  rcases p4984_3 (m.d 0 3) (by simp) with h5001 | h5001
                                                  · linarith only [h5001, h7, hlam]
                                                  · linarith only [h1, h5001, hlam]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4811, h4923, hc12, hc34, hlam, hphi, ht23, p4984_1]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  rcases p4984_3 (m.d 0 3) (by simp) with h5006 | h5006
                                                  · linarith only [h5006, h7, hlam]
                                                  · linarith only [h4553, h5006, hlam]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4553, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4919, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4923, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [h4925, hlam, p4984_0]
                                                · have p4984_0 := h4984c.1
                                                  have p4984_1 := h4984c.2.1
                                                  have p4984_2 := h4984c.2.2.1
                                                  have p4984_3 := h4984c.2.2.2
                                                  linarith only [hlam, p4984_0]
                                      · linarith only [h4975, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      rcases p4963_3 (m.d 0 2) (by simp) with h5015 | h5015
                                      · rcases p4963_3 (m.d 1 2) (by simp) with h5016 | h5016
                                        · linarith only [h0, h5016, hlam]
                                        · rcases p4963_3 (m.d 2 3) (by simp) with h5018 | h5018
                                          · linarith only [h4, h5018, hlam]
                                          · linarith only [h4923, h5018, hlam]
                                      · linarith only [h5015, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4555, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4803, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4811, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, h4921, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4926_1, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4921, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, h4921, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p4926_1, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h5, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4926_1, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p4926_1, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h0, h4811, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4926_1, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h6, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4553, h6, h7, hc12, hc34, hlam, hphi, ht23, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4923, hlam, p4963_1]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [h4924, hlam, p4963_0]
                                    · have p4963_0 := h4963c.1
                                      have p4963_1 := h4963c.2.1
                                      have p4963_2 := h4963c.2.2.1
                                      have p4963_3 := h4963c.2.2.2
                                      linarith only [hlam, p4963_0]
                            · linarith only [h4956, h5, hlam]
                          · linarith only [h2, h4955, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          rcases p4926_3 (m.d 0 1) (by simp) with h5044 | h5044
                          · rcases p4926_3 (m.d 0 2) (by simp) with h5045 | h5045
                            · rcases p4926_3 (m.d 0 3) (by simp) with h5046 | h5046
                              · linarith only [h4, h5046, hlam]
                              · linarith only [h4553, h5046, hlam]
                            · linarith only [h5045, h6, hlam]
                          · linarith only [h3, h5044, hlam]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h1, hlam, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4, hlam, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h7, hlam, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h3, h4811, h7, hc12, hc34, hlam, hphi, ht23, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h2, hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h5, hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4, h4555, h7, hc12, hc34, hlam, hphi, ht23, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4811, h6, h7, hc12, hc34, hlam, hphi, ht23, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h3, hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h6, hlam, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4553, hlam, p4926_0]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [h4554, hlam, p4926_1]
                        · have p4926_0 := h4926c.1
                          have p4926_1 := h4926c.2.1
                          have p4926_2 := h4926c.2.2.1
                          have p4926_3 := h4926c.2.2.2
                          linarith only [hlam, p4926_0]
                      · linarith only [h4553, h4811, h4925, h6, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h3, h4553, h4803, h4920, h4924, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4555, h4919, h4923, hlam]
              · linarith only [h4917, h4919, h4920, hlam]
            · linarith only [h4553, h4919, h7, hc13, hc34, hlam, hphi]
  · linarith only [h4553, h4554, h7, hlam]

end R2N4
