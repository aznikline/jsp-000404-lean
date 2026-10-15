import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S37
import Jsp000404.R1LeavesN7_3S38

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16564 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h16565 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 2 4 (by decide) (by decide) with h17254 | h17254
  · rcases m.htr 0 2 5 (by decide) (by decide) with h17255 | h17255
    · rcases m.htr 0 3 4 (by decide) (by decide) with h17256 | h17256
      · rcases m.htr 0 3 5 (by decide) (by decide) with h17257 | h17257
        · rcases m.htr 0 4 5 (by decide) (by decide) with h17258 | h17258
          · rcases m.htr 1 2 3 (by decide) (by decide) with h17259 | h17259
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17260 | h17260
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17261 | h17261
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17262 | h17262
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17263 | h17263
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17264 | h17264
                      · linarith only [h0, h16563, h16565, h17259, h17264, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h16563, h16565, h17258, h17259, h17264, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h16564, h16565, h17257, h17259, h17263, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h14799, h17256, h17262, hlam]
                · linarith only [h0, h16563, h16565, h17259, h17260, h17261, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · linarith only [h0, h16563, h16565, h17259, h17260, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17271 | h17271
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17272 | h17272
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17273 | h17273
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17274 | h17274
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17275 | h17275
                      · linarith only [h0, h16563, h17259, h17275, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h16563, h17258, h17259, h17275, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h14799, h17257, h17274, hlam]
                  · linarith only [h14799, h17256, h17273, hlam]
                · linarith only [h0, h16564, h17255, h17272, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h17254, h17271, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h17282 | h17282
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17283 | h17283
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17284 | h17284
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17285 | h17285
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17286 | h17286
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17287 | h17287
                      · linarith only [h16563, h17258, h17287, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17289 | h17289
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17290 | h17290
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17291 | h17291
                            · linarith only [h16563, h17258, h17283, h17291, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17293 | h17293
                              · linarith only [h16563, h17258, h17283, h17289, h17293, hlam]
                              · rcases h1bigk with h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c | h17295c
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h14799, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, h16565, h17282, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, h16565, h17282, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  rcases p17295_3 (m.d 0 1) (by simp) with h17301 | h17301
                                  · linarith only [h17301, hlam, p17295_0]
                                  · rcases p17295_3 (m.d 1 2) (by simp) with h17303 | h17303
                                    · rcases p17295_3 (m.d 1 3) (by simp) with h17304 | h17304
                                      · linarith only [h17282, h17304, hlam]
                                      · linarith only [h14799, h17304, hlam]
                                    · linarith only [h17303, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, h16564, h16565, h17282, h17287, hlam, p17295_2]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, h16564, h16565, h17282, hlam, p17295_2]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  rcases p17295_3 (m.d 0 1) (by simp) with h17312 | h17312
                                  · linarith only [h17312, hlam, p17295_0]
                                  · rcases p17295_3 (m.d 1 2) (by simp) with h17314 | h17314
                                    · rcases p17295_3 (m.d 1 3) (by simp) with h17315 | h17315
                                      · rcases p17295_3 (m.d 1 4) (by simp) with h17316 | h17316
                                        · linarith only [h17285, h17316, hlam]
                                        · rcases p17295_3 (m.d 1 5) (by simp) with h17318 | h17318
                                          · linarith only [h17286, h17318, hlam]
                                          · rcases h3bigk with h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c | h17320c
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h14799, hlam, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h16565, hlam, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              rcases p17320_3 (m.d 0 3) (by simp) with h17324 | h17324
                                              · rcases p17320_3 (m.d 1 3) (by simp) with h17325 | h17325
                                                · rcases p17320_3 (m.d 2 3) (by simp) with h17326 | h17326
                                                  · rcases p17320_3 (m.d 3 4) (by simp) with h17327 | h17327
                                                    · linarith only [h17327, hlam, p17320_0]
                                                    · rcases p17320_3 (m.d 3 5) (by simp) with h17329 | h17329
                                                      · linarith only [h17257, h17329, hlam]
                                                      · linarith only [h17293, h17329, hlam]
                                                  · linarith only [h17289, h17326, hlam]
                                                · linarith only [h17285, h17325, hlam]
                                              · linarith only [h17324, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              rcases p17320_3 (m.d 0 3) (by simp) with h17335 | h17335
                                              · rcases p17320_3 (m.d 1 3) (by simp) with h17336 | h17336
                                                · rcases p17320_3 (m.d 2 3) (by simp) with h17337 | h17337
                                                  · rcases p17320_3 (m.d 3 4) (by simp) with h17338 | h17338
                                                    · linarith only [h17256, h17338, hlam]
                                                    · rcases p17320_3 (m.d 3 5) (by simp) with h17340 | h17340
                                                      · linarith only [h17340, hlam, p17320_0]
                                                      · rcases h5bigk with h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c | h17342c
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h0, h16564, h16565, h17282, h17283, h17287, h17289, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h0, h16564, h16565, h17282, h17289, h17291, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h0, h16564, h16565, h17282, h17293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17258, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h16564, hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h0, h16564, h16565, h17282, h17289, h17291, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h0, h16564, h16565, h17282, h17293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17287, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17255, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17284, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h16565, h17255, h17282, h17293, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17291, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17257, hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17286, hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17290, hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [hlam, p17342_0]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17293, hlam, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17257, h17293, hc34, hc45, hlam, hphi, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17286, h17293, hc34, hc45, hlam, hphi, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17290, h17293, hc34, hc45, hlam, hphi, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [h17293, hc34, hc45, hlam, hphi, p17342_1]
                                                        · have p17342_0 := h17342c.1
                                                          have p17342_1 := h17342c.2.1
                                                          have p17342_2 := h17342c.2.2.1
                                                          have p17342_3 := h17342c.2.2.2
                                                          linarith only [hlam, p17342_0]
                                                  · linarith only [h17290, h17337, hlam]
                                                · linarith only [h17286, h17336, hlam]
                                              · linarith only [h17335, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              rcases p17320_3 (m.d 0 3) (by simp) with h17371 | h17371
                                              · linarith only [h14799, h17371, hlam]
                                              · rcases p17320_3 (m.d 1 3) (by simp) with h17373 | h17373
                                                · rcases p17320_3 (m.d 2 3) (by simp) with h17374 | h17374
                                                  · linarith only [h17282, h17374, hlam]
                                                  · linarith only [h16565, h17374, hlam]
                                                · linarith only [h14799, h17373, hlam]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h0, h16565, h17282, hc01, hc12, hlam, hphi, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h16564, h17283, h17287, h17289, hlam, p17295_1, p17320_2]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h16564, h17284, h17290, hlam, p17295_1, p17320_2]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h16565, h17255, h17282, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17282, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              rcases p17320_3 (m.d 0 3) (by simp) with h17385 | h17385
                                              · linarith only [h16565, h17385, hlam]
                                              · linarith only [h17256, h17385, hlam]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              rcases p17320_3 (m.d 0 3) (by simp) with h17388 | h17388
                                              · linarith only [h16565, h17388, hlam]
                                              · linarith only [h17257, h17388, hlam]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17256, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17285, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17289, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17293, hlam, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17257, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17286, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h17290, hlam, p17320_0]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [h16565, h17257, h17282, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17320_1]
                                            · have p17320_0 := h17320c.1
                                              have p17320_1 := h17320c.2.1
                                              have p17320_2 := h17320c.2.2.1
                                              have p17320_3 := h17320c.2.2.2
                                              linarith only [hlam, p17320_0]
                                      · linarith only [h17315, hlam, p17295_0]
                                    · linarith only [h0, h17314, hlam]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17282, hlam, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  rcases p17295_3 (m.d 0 1) (by simp) with h17405 | h17405
                                  · linarith only [h14799, h17405, hlam]
                                  · linarith only [h16563, h17405, hlam]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  rcases p17295_3 (m.d 0 1) (by simp) with h17408 | h17408
                                  · linarith only [h14799, h17408, hlam]
                                  · linarith only [h16564, h17408, hlam]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h16563, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17283, hlam, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17285, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17287, hlam, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h16564, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17284, hlam, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h17286, hlam, p17295_0]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [h0, h16564, h17283, h17289, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17295_1]
                                · have p17295_0 := h17295c.1
                                  have p17295_1 := h17295c.2.1
                                  have p17295_2 := h17295c.2.2.1
                                  have p17295_3 := h17295c.2.2.2
                                  linarith only [hlam, p17295_0]
                          · linarith only [h0, h16564, h16565, h17286, h17290, hlam]
                        · linarith only [h16565, h17256, h17289, hlam]
                    · linarith only [h16565, h17257, h17282, h17286, hlam]
                  · linarith only [h14799, h17256, h17285, hlam]
                · linarith only [h0, h16565, h17282, h17284, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h16565, h17282, h17283, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h17427 | h17427
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17428 | h17428
                · rcases m.htr 1 3 4 (by decide) (by decide) with h17429 | h17429
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h17430 | h17430
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h17431 | h17431
                      · linarith only [h0, h16563, h17282, h17431, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17433 | h17433
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h17434 | h17434
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h17435 | h17435
                            · linarith only [h16563, h17258, h17427, h17435, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h17437 | h17437
                              · linarith only [h16563, h17258, h17427, h17433, h17437, hlam]
                              · rcases h1bigk with h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c | h17439c
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h0, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h14799, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h0, h17282, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h0, h17282, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17282, hc01, hc23, hlam, hphi, ht12, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17282, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  rcases p17439_3 (m.d 0 1) (by simp) with h17448 | h17448
                                  · linarith only [h0, h17448, hlam]
                                  · linarith only [h16563, h17448, hlam]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  rcases p17439_3 (m.d 0 1) (by simp) with h17451 | h17451
                                  · linarith only [h0, h17451, hlam]
                                  · linarith only [h16564, h17451, hlam]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  rcases p17439_3 (m.d 0 1) (by simp) with h17454 | h17454
                                  · linarith only [h17454, hlam, p17439_0]
                                  · rcases p17439_3 (m.d 1 2) (by simp) with h17456 | h17456
                                    · linarith only [h17282, h17456, hlam]
                                    · linarith only [h0, h17456, hlam]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h0, h16564, h17282, h17427, h17431, h17433, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  rcases p17439_3 (m.d 0 1) (by simp) with h17461 | h17461
                                  · linarith only [h14799, h17461, hlam]
                                  · linarith only [h16563, h17461, hlam]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  rcases p17439_3 (m.d 0 1) (by simp) with h17464 | h17464
                                  · linarith only [h14799, h17464, hlam]
                                  · linarith only [h16564, h17464, hlam]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h16563, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17427, hlam, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17429, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17431, hlam, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h16564, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17428, hlam, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h17430, hlam, p17439_0]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [h0, h16564, h17427, h17433, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17439_1]
                                · have p17439_0 := h17439c.1
                                  have p17439_1 := h17439c.2.1
                                  have p17439_2 := h17439c.2.2.1
                                  have p17439_3 := h17439c.2.2.2
                                  linarith only [hlam, p17439_0]
                          · linarith only [h0, h17282, h17434, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h16564, h17282, h17427, h17431, h17433, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h14799, h17257, h17430, hlam]
                  · linarith only [h14799, h17256, h17429, hlam]
                · linarith only [h0, h14799, h16565, h17255, h17428, hc01, hc13, hlam, hphi]
              · linarith only [h0, h17254, h17427, hlam]
        · linarith only [h0, h16564, h16565, h17257, hlam]
      · linarith only [h0, h16563, h16565, h17256, hlam]
    · linarith only [h0, h16564, h17255, hlam]
  · linarith only [h0, h16563, h17254, hlam]

set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16564 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 2 3 (by decide) (by decide) with h16565 | h16565
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0_x0 m hb1 hb3 hb5 hg0 hg14799 h16563 h16564 h16565
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0_x1 m hb1 hb3 hb5 hg0 hg14799 h16563 h16564 h16565

set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h16564 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 2 3 (by decide) (by decide) with h17487 | h17487
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17488 | h17488
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17489 | h17489
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17490 | h17490
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17491 | h17491
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17492 | h17492
            · linarith only [h16563, h16564, h17492, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17494 | h17494
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17495 | h17495
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17496 | h17496
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17497 | h17497
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17498 | h17498
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17499 | h17499
                        · linarith only [h16563, h16564, h17492, h17498, h17499, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17501 | h17501
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17502 | h17502
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17503 | h17503
                              · linarith only [h16563, h16564, h17495, h17499, h17503, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17505 | h17505
                                · linarith only [h16563, h16564, h17495, h17499, h17501, h17505, hlam]
                                · rcases h1bigk with h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c | h17507c
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h0, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h14799, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16564, h17495, h17499, h17501, hc34, hc45, hlam, hphi, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16564, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    rcases p17507_3 (m.d 0 1) (by simp) with h17513 | h17513
                                    · linarith only [h17513, hlam, p17507_0]
                                    · rcases p17507_3 (m.d 1 2) (by simp) with h17515 | h17515
                                      · rcases p17507_3 (m.d 1 3) (by simp) with h17516 | h17516
                                        · linarith only [h17494, h17516, hlam]
                                        · linarith only [h14799, h17516, hlam]
                                      · linarith only [h17515, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h14799, hc01, hc12, hlam, hphi, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    rcases p17507_3 (m.d 0 1) (by simp) with h17522 | h17522
                                    · linarith only [h0, h17522, hlam]
                                    · linarith only [h16563, h17522, hlam]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16563, h16564, h17495, h17501, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    rcases p17507_3 (m.d 0 1) (by simp) with h17526 | h17526
                                    · linarith only [h17526, hlam, p17507_0]
                                    · rcases p17507_3 (m.d 1 2) (by simp) with h17528 | h17528
                                      · rcases p17507_3 (m.d 1 3) (by simp) with h17529 | h17529
                                        · rcases p17507_3 (m.d 1 4) (by simp) with h17530 | h17530
                                          · linarith only [h17497, h17530, hlam]
                                          · rcases p17507_3 (m.d 1 5) (by simp) with h17532 | h17532
                                            · linarith only [h17498, h17532, hlam]
                                            · linarith only [h16564, h17532, hlam]
                                        · linarith only [h17529, hlam, p17507_0]
                                      · linarith only [h0, h17528, hlam]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17494, hlam, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    rcases p17507_3 (m.d 0 1) (by simp) with h17539 | h17539
                                    · linarith only [h14799, h17539, hlam]
                                    · linarith only [h16563, h17539, hlam]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16563, h16564, h17495, h17501, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16563, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17495, hlam, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17497, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17499, hlam, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h16563, h17495, h17499, h17501, hc34, hc45, hlam, hphi, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17496, hlam, p17507_1]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [h17498, hlam, p17507_0]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    rcases p17507_3 (m.d 0 1) (by simp) with h17551 | h17551
                                    · linarith only [h16564, h17551, hlam]
                                    · linarith only [h16563, h17551, hlam]
                                  · have p17507_0 := h17507c.1
                                    have p17507_1 := h17507c.2.1
                                    have p17507_2 := h17507c.2.2.1
                                    have p17507_3 := h17507c.2.2.2
                                    linarith only [hlam, p17507_0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17555 | h17555
                              · linarith only [h16563, h16564, h17495, h17499, h17555, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17557 | h17557
                                · linarith only [h0, h16563, h16564, h17487, h17490, h17495, h17499, h17557, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases h1bigk with h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c | h17559c
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h0, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h14799, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16564, h17495, h17499, h17501, hc34, hc45, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16564, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17565 | h17565
                                    · linarith only [h17565, hlam, p17559_0]
                                    · rcases p17559_3 (m.d 1 2) (by simp) with h17567 | h17567
                                      · rcases p17559_3 (m.d 1 3) (by simp) with h17568 | h17568
                                        · linarith only [h17494, h17568, hlam]
                                        · linarith only [h14799, h17568, hlam]
                                      · linarith only [h17567, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h14799, hc01, hc12, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17574 | h17574
                                    · linarith only [h0, h17574, hlam]
                                    · linarith only [h16563, h17574, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16564, hc01, hc12, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17578 | h17578
                                    · linarith only [h17578, hlam, p17559_0]
                                    · rcases p17559_3 (m.d 1 2) (by simp) with h17580 | h17580
                                      · rcases p17559_3 (m.d 1 3) (by simp) with h17581 | h17581
                                        · rcases p17559_3 (m.d 1 4) (by simp) with h17582 | h17582
                                          · linarith only [h17497, h17582, hlam]
                                          · rcases p17559_3 (m.d 1 5) (by simp) with h17584 | h17584
                                            · linarith only [h17498, h17584, hlam]
                                            · linarith only [h16564, h17584, hlam]
                                        · linarith only [h17581, hlam, p17559_0]
                                      · linarith only [h0, h17580, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17494, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17591 | h17591
                                    · linarith only [h14799, h17591, hlam]
                                    · linarith only [h16563, h17591, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16564, h17491, h17494, h17501, h17502, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16563, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17495, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17497, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17499, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h16563, h17495, h17499, h17501, hc34, hc45, hlam, hphi, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17496, hlam, p17559_1]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [h17498, hlam, p17559_0]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    rcases p17559_3 (m.d 0 1) (by simp) with h17603 | h17603
                                    · linarith only [h16564, h17603, hlam]
                                    · linarith only [h16563, h17603, hlam]
                                  · have p17559_0 := h17559c.1
                                    have p17559_1 := h17559c.2.1
                                    have p17559_2 := h17559c.2.2.1
                                    have p17559_3 := h17559c.2.2.2
                                    linarith only [hlam, p17559_0]
                          · linarith only [h16563, h16564, h17497, h17499, h17501, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h14799, h16563, h17487, h17491, h17498, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h14799, h17490, h17497, hlam]
                  · linarith only [h0, h17489, h17496, hlam]
                · linarith only [h0, h17488, h17495, hlam]
              · linarith only [h0, h17487, h17494, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17613 | h17613
            · linarith only [h14799, h16563, h17491, h17613, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17615 | h17615
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17616 | h17616
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17617 | h17617
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17618 | h17618
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17619 | h17619
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17620 | h17620
                        · linarith only [h14799, h16563, h17491, h17613, h17615, h17619, h17620, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17622 | h17622
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17623 | h17623
                            · linarith only [h14799, h16563, h17487, h17491, h17623, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17625 | h17625
                              · linarith only [h14799, h16563, h17491, h17616, h17619, h17620, h17625, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17627 | h17627
                                · linarith only [h14799, h16563, h17491, h17616, h17619, h17620, h17622, h17627, hlam]
                                · rcases h1bigk with h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c | h17629c
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h0, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h17491, h17616, h17619, h17622, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h16564, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    rcases p17629_3 (m.d 0 1) (by simp) with h17635 | h17635
                                    · linarith only [h17635, hlam, p17629_0]
                                    · rcases p17629_3 (m.d 1 2) (by simp) with h17637 | h17637
                                      · rcases p17629_3 (m.d 1 3) (by simp) with h17638 | h17638
                                        · linarith only [h17615, h17638, hlam]
                                        · linarith only [h14799, h17638, hlam]
                                      · linarith only [h17637, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h17491, h17619, hc01, hc12, hlam, hphi, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h16563, h17491, h17615, h17619, hlam, p17629_2]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h16563, h17491, h17616, h17619, h17622, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    rcases p17629_3 (m.d 0 1) (by simp) with h17646 | h17646
                                    · linarith only [h17646, hlam, p17629_0]
                                    · rcases p17629_3 (m.d 1 2) (by simp) with h17648 | h17648
                                      · rcases p17629_3 (m.d 1 3) (by simp) with h17649 | h17649
                                        · rcases p17629_3 (m.d 1 4) (by simp) with h17650 | h17650
                                          · linarith only [h17618, h17650, hlam]
                                          · rcases p17629_3 (m.d 1 5) (by simp) with h17652 | h17652
                                            · linarith only [h17619, h17652, hlam]
                                            · linarith only [h16564, h17652, hlam]
                                        · linarith only [h17649, hlam, p17629_0]
                                      · linarith only [h0, h17648, hlam]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17615, hlam, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h16563, h17491, h17619, hlam, p17629_2]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h14799, h16563, h17491, h17616, h17619, h17622, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h16563, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17616, hlam, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17618, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17620, hlam, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h16563, h17616, h17620, h17622, hc34, hc45, hlam, hphi, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17617, hlam, p17629_1]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [h17619, hlam, p17629_0]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    rcases p17629_3 (m.d 0 1) (by simp) with h17669 | h17669
                                    · linarith only [h16564, h17669, hlam]
                                    · linarith only [h16563, h17669, hlam]
                                  · have p17629_0 := h17629c.1
                                    have p17629_1 := h17629c.2.1
                                    have p17629_2 := h17629c.2.2.1
                                    have p17629_3 := h17629c.2.2.2
                                    linarith only [hlam, p17629_0]
                          · linarith only [h17490, h17491, h17622, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17674 | h17674
                        · linarith only [h14799, h16563, h17619, h17674, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17676 | h17676
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17677 | h17677
                            · linarith only [h14799, h17619, h17677, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17679 | h17679
                              · linarith only [h14799, h16563, h17616, h17619, h17674, h17679, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17681 | h17681
                                · linarith only [h14799, h16563, h17616, h17619, h17674, h17676, h17681, hlam]
                                · linarith only [h14799, h16563, h17616, h17619, h17676, h17681, hc34, hc45, hlam, hphi]
                          · linarith only [h14799, h17490, h17619, h17676, hc23, hc35, hlam, hphi]
                    · linarith only [h14799, h16563, h17490, h17618, hlam]
                  · linarith only [h0, h17489, h17617, hlam]
                · linarith only [h0, h17488, h17616, hlam]
              · linarith only [h0, h17487, h17615, hlam]
        · linarith only [h14799, h16563, h17490, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17690 | h17690
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17691 | h17691
          · linarith only [h17487, h17489, h17691, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17693 | h17693
            · linarith only [h0, h16563, h17489, h17693, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17695 | h17695
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17696 | h17696
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17697 | h17697
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17698 | h17698
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17699 | h17699
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17700 | h17700
                        · linarith only [h14799, h16563, h17487, h17489, h17693, h17697, h17700, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17702 | h17702
                          · linarith only [h17487, h17489, h17697, h17702, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h17487, h17489, h17690, h17697, h17702, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17705 | h17705
                        · linarith only [h14799, h16563, h17487, h17489, h17697, h17705, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17707 | h17707
                          · linarith only [h17487, h17489, h17697, h17707, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h17487, h17489, h17690, h17697, h17707, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h14799, h16563, h17690, h17698, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17711 | h17711
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17712 | h17712
                      · linarith only [h14799, h17691, h17695, h17697, h17712, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17714 | h17714
                        · linarith only [h0, h16563, h17697, h17714, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17716 | h17716
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17717 | h17717
                            · linarith only [h0, h17487, h17697, h17712, h17717, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17719 | h17719
                              · linarith only [h0, h16563, h16564, h17696, h17697, h17714, h17717, h17719, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h14799, h16563, h17695, h17697, h17719, hc14, hc45, hlam, hphi]
                          · linarith only [h14799, h17690, h17712, h17716, hc23, hc35, hlam, hphi]
                    · linarith only [h14799, h16563, h17690, h17711, hlam]
                · linarith only [h0, h17488, h17696, hlam]
              · linarith only [h0, h17487, h17695, hlam]
        · linarith only [h14799, h16563, h17690, hlam]
    · linarith only [h0, h16563, h17488, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h17728 | h17728
    · rcases m.htr 0 2 5 (by decide) (by decide) with h17729 | h17729
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17730 | h17730
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17731 | h17731
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17732 | h17732
            · linarith only [h16563, h16564, h17732, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17734 | h17734
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17735 | h17735
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17736 | h17736
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17737 | h17737
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17738 | h17738
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17739 | h17739
                        · linarith only [h16563, h16564, h17487, h17729, h17732, h17734, h17739, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17741 | h17741
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17742 | h17742
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17743 | h17743
                              · linarith only [h16563, h16564, h17735, h17739, h17743, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17745 | h17745
                                · linarith only [h16563, h16564, h17735, h17739, h17741, h17745, hlam]
                                · rcases h1bigk with h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c | h17747c
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h0, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h14799, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16564, h17487, h17729, h17734, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16564, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    rcases p17747_3 (m.d 0 1) (by simp) with h17753 | h17753
                                    · linarith only [h17753, hlam, p17747_0]
                                    · rcases p17747_3 (m.d 1 2) (by simp) with h17755 | h17755
                                      · rcases p17747_3 (m.d 1 3) (by simp) with h17756 | h17756
                                        · linarith only [h17734, h17756, hlam]
                                        · linarith only [h14799, h17756, hlam]
                                      · linarith only [h17755, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16564, h17487, h17729, h17734, hc01, hc12, hlam, hphi, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16563, h16564, h17487, h17729, h17734, hlam, p17747_2]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16563, h16564, h17735, h17741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    rcases p17747_3 (m.d 0 1) (by simp) with h17764 | h17764
                                    · linarith only [h17764, hlam, p17747_0]
                                    · rcases p17747_3 (m.d 1 2) (by simp) with h17766 | h17766
                                      · rcases p17747_3 (m.d 1 3) (by simp) with h17767 | h17767
                                        · rcases p17747_3 (m.d 1 4) (by simp) with h17768 | h17768
                                          · linarith only [h17737, h17768, hlam]
                                          · rcases p17747_3 (m.d 1 5) (by simp) with h17770 | h17770
                                            · linarith only [h17738, h17770, hlam]
                                            · linarith only [h16564, h17770, hlam]
                                        · linarith only [h17767, hlam, p17747_0]
                                      · linarith only [h0, h17766, hlam]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17734, hlam, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    rcases p17747_3 (m.d 0 1) (by simp) with h17777 | h17777
                                    · linarith only [h14799, h17777, hlam]
                                    · linarith only [h16563, h17777, hlam]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16563, h16564, h17735, h17741, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16563, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17735, hlam, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17737, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17739, hlam, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h16563, h17735, h17739, h17741, hc34, hc45, hlam, hphi, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17736, hlam, p17747_1]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [h17738, hlam, p17747_0]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    rcases p17747_3 (m.d 0 1) (by simp) with h17789 | h17789
                                    · linarith only [h16564, h17789, hlam]
                                    · linarith only [h16563, h17789, hlam]
                                  · have p17747_0 := h17747c.1
                                    have p17747_1 := h17747c.2.1
                                    have p17747_2 := h17747c.2.2.1
                                    have p17747_3 := h17747c.2.2.2
                                    linarith only [hlam, p17747_0]
                            · linarith only [h16563, h16564, h17487, h17729, h17731, h17735, h17741, h17742, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h16563, h16564, h17487, h17729, h17730, h17735, h17741, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h14799, h16563, h17487, h17729, h17731, h17734, h17735, h17738, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h17487, h17730, h17734, h17737, hlam]
                  · linarith only [h17487, h17729, h17736, hc12, hc23, hlam, hphi]
                · linarith only [h17487, h17734, h17735, hc02, hc24, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17799 | h17799
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17800 | h17800
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17801 | h17801
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17802 | h17802
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17803 | h17803
                        · linarith only [h16563, h16564, h17734, h17800, h17803, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17805 | h17805
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17806 | h17806
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17807 | h17807
                              · linarith only [h16563, h16564, h17799, h17803, h17807, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17809 | h17809
                                · linarith only [h16563, h16564, h17799, h17803, h17805, h17809, hlam]
                                · rcases h1bigk with h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c | h17811c
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h0, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h14799, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16564, h17734, h17799, h17800, h17805, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16564, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17734, hc01, hc23, hlam, hphi, ht12, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17734, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    rcases p17811_3 (m.d 0 1) (by simp) with h17820 | h17820
                                    · linarith only [h0, h17820, hlam]
                                    · linarith only [h16563, h17820, hlam]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16563, h16564, h17734, h17799, h17805, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    rcases p17811_3 (m.d 0 1) (by simp) with h17824 | h17824
                                    · linarith only [h17824, hlam, p17811_0]
                                    · rcases p17811_3 (m.d 1 2) (by simp) with h17826 | h17826
                                      · linarith only [h17734, h17826, hlam]
                                      · linarith only [h0, h17826, hlam]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h0, h16563, h17734, h17799, h17805, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    rcases p17811_3 (m.d 0 1) (by simp) with h17831 | h17831
                                    · linarith only [h14799, h17831, hlam]
                                    · linarith only [h16563, h17831, hlam]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16563, h16564, h17799, h17805, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16563, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17799, hlam, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17801, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17803, hlam, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h16563, h17799, h17803, h17805, hc34, hc45, hlam, hphi, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17800, hlam, p17811_1]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [h17802, hlam, p17811_0]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    rcases p17811_3 (m.d 0 1) (by simp) with h17843 | h17843
                                    · linarith only [h16564, h17843, hlam]
                                    · linarith only [h16563, h17843, hlam]
                                  · have p17811_0 := h17811c.1
                                    have p17811_1 := h17811c.2.1
                                    have p17811_2 := h17811c.2.2.1
                                    have p17811_3 := h17811c.2.2.2
                                    linarith only [hlam, p17811_0]
                            · linarith only [h0, h16563, h17734, h17799, h17805, h17806, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h16564, h17734, h17800, h17805, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h14799, h16563, h17729, h17731, h17734, h17799, h17802, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h14799, h17730, h17801, hlam]
                  · linarith only [h0, h16563, h17729, h17799, h17800, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h17728, h17799, hlam]
          · linarith only [h17487, h17729, h17731, hlam]
        · linarith only [h0, h16563, h17487, h17730, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h17855 | h17855
        · rcases m.htr 0 3 5 (by decide) (by decide) with h17856 | h17856
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17857 | h17857
            · linarith only [h0, h16563, h17729, h17857, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17859 | h17859
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17860 | h17860
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17861 | h17861
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17862 | h17862
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17863 | h17863
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17864 | h17864
                        · linarith only [h0, h16563, h17487, h17857, h17859, h17864, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17866 | h17866
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17867 | h17867
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17868 | h17868
                              · linarith only [h0, h16563, h17729, h17860, h17861, h17864, h17868, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17870 | h17870
                                · linarith only [h0, h16563, h17729, h17860, h17861, h17864, h17866, h17870, hlam]
                                · rcases h1bigk with h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c | h17872c
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h14799, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, h17729, h17859, h17867, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h16564, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    rcases p17872_3 (m.d 0 1) (by simp) with h17878 | h17878
                                    · linarith only [h17878, hlam, p17872_0]
                                    · rcases p17872_3 (m.d 1 2) (by simp) with h17880 | h17880
                                      · rcases p17872_3 (m.d 1 3) (by simp) with h17881 | h17881
                                        · linarith only [h17859, h17881, hlam]
                                        · linarith only [h14799, h17881, hlam]
                                      · linarith only [h17880, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, h17729, h17861, h17863, hc01, hc12, hlam, hphi, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, h16563, h17487, h17859, hlam, p17872_2]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, h16563, h17729, h17860, h17861, h17866, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    rcases p17872_3 (m.d 0 1) (by simp) with h17889 | h17889
                                    · linarith only [h17889, hlam, p17872_0]
                                    · rcases p17872_3 (m.d 1 2) (by simp) with h17891 | h17891
                                      · rcases p17872_3 (m.d 1 3) (by simp) with h17892 | h17892
                                        · rcases p17872_3 (m.d 1 4) (by simp) with h17893 | h17893
                                          · linarith only [h17862, h17893, hlam]
                                          · rcases p17872_3 (m.d 1 5) (by simp) with h17895 | h17895
                                            · linarith only [h17863, h17895, hlam]
                                            · linarith only [h16564, h17895, hlam]
                                        · linarith only [h17892, hlam, p17872_0]
                                      · linarith only [h0, h17891, hlam]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17859, hlam, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    rcases p17872_3 (m.d 0 1) (by simp) with h17902 | h17902
                                    · linarith only [h14799, h17902, hlam]
                                    · linarith only [h16563, h17902, hlam]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h0, h16563, h17729, h17860, h17861, h17866, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h16563, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17860, hlam, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17862, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17864, hlam, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h16563, h17860, h17864, h17866, hc34, hc45, hlam, hphi, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17861, hlam, p17872_1]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [h17863, hlam, p17872_0]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    rcases p17872_3 (m.d 0 1) (by simp) with h17914 | h17914
                                    · linarith only [h16564, h17914, hlam]
                                    · linarith only [h16563, h17914, hlam]
                                  · have p17872_0 := h17872c.1
                                    have p17872_1 := h17872c.2.1
                                    have p17872_2 := h17872c.2.2.1
                                    have p17872_3 := h17872c.2.2.2
                                    linarith only [hlam, p17872_0]
                            · linarith only [h0, h16563, h17487, h17856, h17860, h17866, h17867, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h16563, h17487, h17855, h17860, h17866, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h14799, h17856, h17863, hlam]
                    · linarith only [h17487, h17855, h17859, h17862, hlam]
                  · linarith only [h0, h16563, h17487, h17859, h17860, h17861, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h16563, h17487, h17859, h17860, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17924 | h17924
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17925 | h17925
                  · linarith only [h0, h16563, h17729, h17859, h17924, h17925, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17927 | h17927
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17928 | h17928
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17929 | h17929
                        · linarith only [h0, h16563, h17857, h17859, h17929, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17931 | h17931
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17932 | h17932
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17933 | h17933
                              · linarith only [h0, h16563, h17924, h17925, h17929, h17932, h17933, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h16563, h17924, h17925, h17931, h17933, hc34, hc45, hlam, hphi]
                            · linarith only [h14799, h17856, h17859, h17932, hlam]
                          · linarith only [h0, h17859, h17931, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h14799, h17856, h17928, hlam]
                    · linarith only [h14799, h17855, h17927, hlam]
                · linarith only [h0, h16563, h17728, h17924, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h17941 | h17941
            · linarith only [h14799, h16563, h17856, h17941, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17943 | h17943
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17944 | h17944
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17945 | h17945
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17946 | h17946
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17947 | h17947
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17948 | h17948
                        · linarith only [h0, h16563, h17487, h17856, h17941, h17943, h17947, h17948, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17950 | h17950
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17951 | h17951
                            · linarith only [h0, h17487, h17856, h17943, h17951, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h16563, h17487, h17944, h17947, h17950, h17951, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h16563, h17487, h17855, h17944, h17950, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17955 | h17955
                        · linarith only [h0, h16563, h17487, h17856, h17941, h17955, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17957 | h17957
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17958 | h17958
                            · linarith only [h14799, h16563, h17944, h17947, h17957, h17958, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17960 | h17960
                              · linarith only [h0, h16563, h17487, h17943, h17944, h17947, h17955, h17960, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h17962 | h17962
                                · linarith only [h0, h16563, h17487, h17944, h17945, h17955, h17957, h17958, h17962, hlam]
                                · linarith only [h0, h16563, h17487, h17943, h17944, h17947, h17957, h17962, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h16563, h17487, h17855, h17944, h17957, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h14799, h16563, h17855, h17946, hlam]
                  · linarith only [h0, h17487, h17943, h17945, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h16563, h17487, h17943, h17944, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17969 | h17969
                · rcases m.htr 1 2 5 (by decide) (by decide) with h17970 | h17970
                  · linarith only [h0, h16563, h17729, h17943, h17969, h17970, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h17972 | h17972
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h17973 | h17973
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17974 | h17974
                        · linarith only [h0, h16563, h17943, h17974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17976 | h17976
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17977 | h17977
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h17978 | h17978
                              · linarith only [h0, h16563, h17487, h17856, h17943, h17969, h17973, h17974, h17978, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h16563, h17969, h17970, h17976, h17978, hc34, hc45, hlam, hphi]
                            · linarith only [h17943, h17973, h17977, hlam]
                          · linarith only [h0, h16563, h17487, h17856, h17943, h17969, h17973, h17976, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h17983 | h17983
                        · linarith only [h0, h16563, h17941, h17943, h17973, h17983, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h17985 | h17985
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h17986 | h17986
                            · linarith only [h0, h16563, h17943, h17969, h17973, h17985, h17986, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h16563, h17943, h17969, h17985, h17986, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h16563, h17943, h17969, h17985, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h16563, h17855, h17943, h17972, hlam]
                · linarith only [h0, h17728, h17969, hlam]
        · linarith only [h14799, h16563, h17855, hlam]
    · linarith only [h0, h16563, h17728, hlam]

set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 1 5 (by decide) (by decide) with h16564 | h16564
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x0 m hb1 hb3 hb5 hg0 hg14799 h16563 h16564
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x0_x1 m hb1 hb3 hb5 hg0 hg14799 h16563 h16564

set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  exact r1l7_11_13_25_L_I_L_I_H_I_s15 m hb1 hb3 hb5 h0 h14799 h16563

set_option maxHeartbeats 16110000 in
set_option maxHeartbeats 16110000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s14 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  rcases m.htr 0 1 4 (by decide) (by decide) with h16563 | h16563
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x0 m hb1 hb3 hb5 hg0 hg14799 h16563
  · exact r1l7_11_13_25_L_I_L_I_H_I_s14_x1 m hb1 hb3 hb5 hg0 hg14799 h16563

end R2N4
