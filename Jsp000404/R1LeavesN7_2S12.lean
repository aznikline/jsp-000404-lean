import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5198000 in
set_option maxHeartbeats 5198000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s13_x0_x0_x1_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9250 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h9251 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9252 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9253 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9255 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9257 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9259 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h9260 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  have h9250 := hg9250
  rcases m.htr 1 4 5 (by decide) (by decide) with h9261 | h9261
  · rcases m.htr 2 3 4 (by decide) (by decide) with h9262 | h9262
    · rcases m.htr 2 3 5 (by decide) (by decide) with h9263 | h9263
      · rcases m.htr 2 4 5 (by decide) (by decide) with h9264 | h9264
        · rcases m.htr 3 4 5 (by decide) (by decide) with h9265 | h9265
          · rcases h0bigk with h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c | h9266c
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9268 | h9268
              · rcases p9266_3 (m.d 0 2) (by simp) with h9269 | h9269
                · linarith only [h0, h9269, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9271 | h9271
                  · linarith only [h1, h9271, hlam]
                  · linarith only [h4, h9271, hlam]
              · linarith only [h0, h9268, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h1, h9259, h9265, hc01, hc45, hlam, hphi, ht0b, ht5b, p9266_1]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9276 | h9276
              · rcases p9266_3 (m.d 0 2) (by simp) with h9277 | h9277
                · linarith only [h0, h9277, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9279 | h9279
                  · linarith only [h1, h9279, hlam]
                  · linarith only [h9250, h9279, hlam]
              · linarith only [h2, h9276, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9283 | h9283
              · rcases p9266_3 (m.d 0 2) (by simp) with h9284 | h9284
                · linarith only [h0, h9284, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9286 | h9286
                  · linarith only [h1, h9286, hlam]
                  · linarith only [h9251, h9286, hlam]
              · linarith only [h3, h9283, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h0, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h4, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h7337, hlam, p9266_1]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h8360, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h1, hlam, p9266_1]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9296 | h9296
              · rcases p9266_3 (m.d 0 2) (by simp) with h9297 | h9297
                · linarith only [h4, h9297, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9299 | h9299
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9300 | h9300
                    · linarith only [h9250, h9300, hlam]
                    · linarith only [h7337, h9300, hlam]
                  · linarith only [h4, h9299, hlam]
              · linarith only [h0, h9296, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9306 | h9306
              · rcases p9266_3 (m.d 0 2) (by simp) with h9307 | h9307
                · linarith only [h4, h9307, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9309 | h9309
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9310 | h9310
                    · linarith only [h9250, h9310, hlam]
                    · rcases p9266_3 (m.d 0 5) (by simp) with h9312 | h9312
                      · linarith only [h9251, h9312, hlam]
                      · rcases h2bigk with h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h4, h8360, h9252, hc12, hc23, hlam, hphi, p9266_1, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h4, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h7337, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h8360, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h0, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9253, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9255, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9257, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9325 | h9325
                          · linarith only [h9325, hlam, p9314_0]
                          · rcases p9314_3 (m.d 1 2) (by simp) with h9327 | h9327
                            · linarith only [h9253, h9327, hlam]
                            · rcases p9314_3 (m.d 2 3) (by simp) with h9329 | h9329
                              · rcases p9314_3 (m.d 2 4) (by simp) with h9330 | h9330
                                · linarith only [h9262, h9330, hlam]
                                · linarith only [h7337, h9330, hlam]
                              · linarith only [h9329, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9334 | h9334
                          · linarith only [h4, h9334, hlam]
                          · linarith only [h0, h9334, hlam]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h8360, h9264, hc02, hc23, hlam, hphi, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9340 | h9340
                          · linarith only [h9340, hlam, p9314_0]
                          · rcases p9314_3 (m.d 1 2) (by simp) with h9342 | h9342
                            · linarith only [h9255, h9342, hlam]
                            · rcases p9314_3 (m.d 2 3) (by simp) with h9344 | h9344
                              · rcases p9314_3 (m.d 2 4) (by simp) with h9345 | h9345
                                · rcases p9314_3 (m.d 2 5) (by simp) with h9346 | h9346
                                  · linarith only [h9264, h9346, hlam]
                                  · linarith only [h8360, h9346, hlam]
                                · linarith only [h9345, hlam, p9314_0]
                              · linarith only [h4, h9344, hlam]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9351 | h9351
                          · linarith only [h7337, h9351, hlam]
                          · linarith only [h0, h9351, hlam]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9262, hlam, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9357 | h9357
                          · linarith only [h9357, hlam, p9314_0]
                          · rcases p9314_3 (m.d 1 2) (by simp) with h9359 | h9359
                            · linarith only [h9257, h9359, hlam]
                            · rcases p9314_3 (m.d 2 3) (by simp) with h9361 | h9361
                              · rcases p9314_3 (m.d 2 4) (by simp) with h9362 | h9362
                                · rcases p9314_3 (m.d 2 5) (by simp) with h9363 | h9363
                                  · rcases h3bigk with h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c | h9364c
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h4, h9259, h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h4, hlam, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h4, h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      rcases p9364_3 (m.d 0 3) (by simp) with h9369 | h9369
                                      · rcases p9364_3 (m.d 1 3) (by simp) with h9370 | h9370
                                        · linarith only [h1, h9370, hlam]
                                        · linarith only [h9260, h9370, hlam]
                                      · linarith only [h9369, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h1, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9253, hlam, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9265, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9266_1, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      rcases p9364_3 (m.d 0 3) (by simp) with h9383 | h9383
                                      · linarith only [h4, h9383, hlam]
                                      · linarith only [h9251, h9383, hlam]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9250, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9259, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9262, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h2, h9259, h9265, hc03, hc45, hlam, hphi, ht0b, ht5b, p9266_1, p9364_1]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9251, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9260, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9263, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [h9265, hlam, p9364_0]
                                    · have p9364_0 := h9364c.1
                                      have p9364_1 := h9364c.2.1
                                      have p9364_2 := h9364c.2.2.1
                                      have p9364_3 := h9364c.2.2.2
                                      linarith only [hlam, p9364_0]
                                  · linarith only [h9363, hlam, p9314_0]
                                · linarith only [h7337, h9362, hlam]
                              · linarith only [h4, h9361, hlam]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          rcases p9314_3 (m.d 0 2) (by simp) with h9399 | h9399
                          · linarith only [h8360, h9399, hlam]
                          · linarith only [h0, h9399, hlam]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9263, hlam, p9314_1]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [h9264, hlam, p9314_0]
                        · have p9314_0 := h9314c.1
                          have p9314_1 := h9314c.2.1
                          have p9314_2 := h9314c.2.2.1
                          have p9314_3 := h9314c.2.2.2
                          linarith only [hlam, p9314_0]
                  · linarith only [h9250, h9309, hlam]
              · linarith only [h2, h9306, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9407 | h9407
              · rcases p9266_3 (m.d 0 2) (by simp) with h9408 | h9408
                · linarith only [h4, h9408, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9410 | h9410
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9411 | h9411
                    · linarith only [h9250, h9411, hlam]
                    · linarith only [h9252, h9411, hlam]
                  · linarith only [h9251, h9410, hlam]
              · linarith only [h3, h9407, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h2, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9417 | h9417
              · rcases p9266_3 (m.d 0 2) (by simp) with h9418 | h9418
                · linarith only [h7337, h9418, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9420 | h9420
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9421 | h9421
                    · rcases p9266_3 (m.d 0 5) (by simp) with h9422 | h9422
                      · linarith only [h9252, h9422, hlam]
                      · linarith only [h8360, h9422, hlam]
                    · linarith only [h7337, h9421, hlam]
                  · linarith only [h4, h9420, hlam]
              · linarith only [h0, h9417, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h9250, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9430 | h9430
              · rcases p9266_3 (m.d 0 2) (by simp) with h9431 | h9431
                · linarith only [h7337, h9431, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9433 | h9433
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9434 | h9434
                    · rcases p9266_3 (m.d 0 5) (by simp) with h9435 | h9435
                      · linarith only [h9252, h9435, hlam]
                      · rcases h2bigk with h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c | h9437c
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h4, hc12, hc23, hlam, hphi, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h4, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h7337, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h8360, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h0, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9253, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9255, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9257, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9448 | h9448
                          · linarith only [h9448, hlam, p9437_0]
                          · rcases p9437_3 (m.d 1 2) (by simp) with h9450 | h9450
                            · linarith only [h9253, h9450, hlam]
                            · rcases p9437_3 (m.d 2 3) (by simp) with h9452 | h9452
                              · rcases p9437_3 (m.d 2 4) (by simp) with h9453 | h9453
                                · linarith only [h9262, h9453, hlam]
                                · linarith only [h7337, h9453, hlam]
                              · linarith only [h9452, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9457 | h9457
                          · linarith only [h4, h9457, hlam]
                          · linarith only [h0, h9457, hlam]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h7337, hc02, hc23, hlam, hphi, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9463 | h9463
                          · linarith only [h9463, hlam, p9437_0]
                          · rcases p9437_3 (m.d 1 2) (by simp) with h9465 | h9465
                            · linarith only [h9255, h9465, hlam]
                            · rcases p9437_3 (m.d 2 3) (by simp) with h9467 | h9467
                              · rcases p9437_3 (m.d 2 4) (by simp) with h9468 | h9468
                                · rcases p9437_3 (m.d 2 5) (by simp) with h9469 | h9469
                                  · linarith only [h9264, h9469, hlam]
                                  · linarith only [h8360, h9469, hlam]
                                · linarith only [h9468, hlam, p9437_0]
                              · linarith only [h4, h9467, hlam]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9474 | h9474
                          · linarith only [h7337, h9474, hlam]
                          · linarith only [h0, h9474, hlam]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9262, hlam, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9480 | h9480
                          · linarith only [h9480, hlam, p9437_0]
                          · rcases p9437_3 (m.d 1 2) (by simp) with h9482 | h9482
                            · linarith only [h9257, h9482, hlam]
                            · rcases p9437_3 (m.d 2 3) (by simp) with h9484 | h9484
                              · rcases p9437_3 (m.d 2 4) (by simp) with h9485 | h9485
                                · rcases p9437_3 (m.d 2 5) (by simp) with h9486 | h9486
                                  · rcases h3bigk with h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c | h9487c
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h4, h9259, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h4, hlam, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h4, h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      rcases p9487_3 (m.d 0 3) (by simp) with h9492 | h9492
                                      · rcases p9487_3 (m.d 1 3) (by simp) with h9493 | h9493
                                        · linarith only [h1, h9493, hlam]
                                        · linarith only [h9260, h9493, hlam]
                                      · linarith only [h9492, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h1, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9253, hlam, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9265, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h1, h9265, hc01, hc45, hlam, hphi, ht0b, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      rcases p9487_3 (m.d 0 3) (by simp) with h9506 | h9506
                                      · linarith only [h4, h9506, hlam]
                                      · linarith only [h9251, h9506, hlam]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9250, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9259, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9262, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9259, h9265, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9487_1]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9251, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9260, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9263, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [h9265, hlam, p9487_0]
                                    · have p9487_0 := h9487c.1
                                      have p9487_1 := h9487c.2.1
                                      have p9487_2 := h9487c.2.2.1
                                      have p9487_3 := h9487c.2.2.2
                                      linarith only [hlam, p9487_0]
                                  · linarith only [h9486, hlam, p9437_0]
                                · linarith only [h7337, h9485, hlam]
                              · linarith only [h4, h9484, hlam]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          rcases p9437_3 (m.d 0 2) (by simp) with h9522 | h9522
                          · linarith only [h8360, h9522, hlam]
                          · linarith only [h0, h9522, hlam]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9263, hlam, p9437_1]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [h9264, hlam, p9437_0]
                        · have p9437_0 := h9437c.1
                          have p9437_1 := h9437c.2.1
                          have p9437_2 := h9437c.2.2.1
                          have p9437_3 := h9437c.2.2.2
                          linarith only [hlam, p9437_0]
                    · linarith only [h9252, h9434, hlam]
                  · linarith only [h9251, h9433, hlam]
              · linarith only [h3, h9430, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h3, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              rcases p9266_3 (m.d 0 1) (by simp) with h9532 | h9532
              · rcases p9266_3 (m.d 0 2) (by simp) with h9533 | h9533
                · linarith only [h8360, h9533, hlam]
                · rcases p9266_3 (m.d 0 3) (by simp) with h9535 | h9535
                  · rcases p9266_3 (m.d 0 4) (by simp) with h9536 | h9536
                    · rcases p9266_3 (m.d 0 5) (by simp) with h9537 | h9537
                      · rcases h2bigk with h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c | h9538c
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9266_1, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h4, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h7337, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h8360, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h0, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9253, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9255, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9257, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9549 | h9549
                          · linarith only [h9549, hlam, p9538_0]
                          · rcases p9538_3 (m.d 1 2) (by simp) with h9551 | h9551
                            · linarith only [h9253, h9551, hlam]
                            · rcases p9538_3 (m.d 2 3) (by simp) with h9553 | h9553
                              · rcases p9538_3 (m.d 2 4) (by simp) with h9554 | h9554
                                · linarith only [h9262, h9554, hlam]
                                · linarith only [h7337, h9554, hlam]
                              · linarith only [h9553, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9558 | h9558
                          · linarith only [h4, h9558, hlam]
                          · linarith only [h0, h9558, hlam]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h7337, hc02, hc23, hlam, hphi, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9564 | h9564
                          · linarith only [h9564, hlam, p9538_0]
                          · rcases p9538_3 (m.d 1 2) (by simp) with h9566 | h9566
                            · linarith only [h9255, h9566, hlam]
                            · rcases p9538_3 (m.d 2 3) (by simp) with h9568 | h9568
                              · rcases p9538_3 (m.d 2 4) (by simp) with h9569 | h9569
                                · rcases p9538_3 (m.d 2 5) (by simp) with h9570 | h9570
                                  · linarith only [h9264, h9570, hlam]
                                  · linarith only [h8360, h9570, hlam]
                                · linarith only [h9569, hlam, p9538_0]
                              · linarith only [h4, h9568, hlam]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9575 | h9575
                          · linarith only [h7337, h9575, hlam]
                          · linarith only [h0, h9575, hlam]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9262, hlam, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9266_1, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9581 | h9581
                          · linarith only [h9581, hlam, p9538_0]
                          · rcases p9538_3 (m.d 1 2) (by simp) with h9583 | h9583
                            · linarith only [h9257, h9583, hlam]
                            · rcases p9538_3 (m.d 2 3) (by simp) with h9585 | h9585
                              · rcases p9538_3 (m.d 2 4) (by simp) with h9586 | h9586
                                · rcases p9538_3 (m.d 2 5) (by simp) with h9587 | h9587
                                  · rcases h3bigk with h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c | h9588c
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h4, h9259, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h4, hlam, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h4, h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      rcases p9588_3 (m.d 0 3) (by simp) with h9593 | h9593
                                      · rcases p9588_3 (m.d 1 3) (by simp) with h9594 | h9594
                                        · linarith only [h1, h9594, hlam]
                                        · linarith only [h9260, h9594, hlam]
                                      · linarith only [h9593, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h1, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9253, hlam, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9265, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h1, h9265, hc01, hc45, hlam, hphi, ht0b, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h2, h9250, h9259, h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9265, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      rcases p9588_3 (m.d 0 3) (by simp) with h9607 | h9607
                                      · linarith only [h4, h9607, hlam]
                                      · linarith only [h9251, h9607, hlam]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9250, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9259, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9262, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9259, h9265, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p9588_1]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9251, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9260, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9263, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [h9265, hlam, p9588_0]
                                    · have p9588_0 := h9588c.1
                                      have p9588_1 := h9588c.2.1
                                      have p9588_2 := h9588c.2.2.1
                                      have p9588_3 := h9588c.2.2.2
                                      linarith only [hlam, p9588_0]
                                  · linarith only [h9587, hlam, p9538_0]
                                · linarith only [h7337, h9586, hlam]
                              · linarith only [h4, h9585, hlam]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          rcases p9538_3 (m.d 0 2) (by simp) with h9623 | h9623
                          · linarith only [h8360, h9623, hlam]
                          · linarith only [h0, h9623, hlam]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9263, hlam, p9538_1]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [h9264, hlam, p9538_0]
                        · have p9538_0 := h9538c.1
                          have p9538_1 := h9538c.2.1
                          have p9538_2 := h9538c.2.2.1
                          have p9538_3 := h9538c.2.2.2
                          linarith only [hlam, p9538_0]
                      · linarith only [h8360, h9537, hlam]
                    · linarith only [h7337, h9536, hlam]
                  · linarith only [h4, h9535, hlam]
              · linarith only [h0, h9532, hlam]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h9251, hlam, p9266_0]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [h9252, hlam, p9266_1]
            · have p9266_0 := h9266c.1
              have p9266_1 := h9266c.2.1
              have p9266_2 := h9266c.2.2.1
              have p9266_3 := h9266c.2.2.2
              linarith only [hlam, p9266_0]
          · rcases h0bigk with h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c | h9636c
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9638 | h9638
              · rcases p9636_3 (m.d 0 2) (by simp) with h9639 | h9639
                · linarith only [h0, h9639, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9641 | h9641
                  · linarith only [h1, h9641, hlam]
                  · linarith only [h4, h9641, hlam]
              · linarith only [h0, h9638, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h1, h9259, h9261, h9265, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h2, h9261, h9265, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9647 | h9647
              · rcases p9636_3 (m.d 0 2) (by simp) with h9648 | h9648
                · linarith only [h0, h9648, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9650 | h9650
                  · linarith only [h1, h9650, hlam]
                  · linarith only [h9251, h9650, hlam]
              · linarith only [h3, h9647, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h0, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h4, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h7337, hlam, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h8360, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h1, hlam, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9660 | h9660
              · rcases p9636_3 (m.d 0 2) (by simp) with h9661 | h9661
                · linarith only [h4, h9661, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9663 | h9663
                  · rcases p9636_3 (m.d 0 4) (by simp) with h9664 | h9664
                    · linarith only [h9250, h9664, hlam]
                    · linarith only [h7337, h9664, hlam]
                  · linarith only [h4, h9663, hlam]
              · linarith only [h0, h9660, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h2, h9261, h9265, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9671 | h9671
              · rcases p9636_3 (m.d 0 2) (by simp) with h9672 | h9672
                · linarith only [h4, h9672, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9674 | h9674
                  · rcases p9636_3 (m.d 0 4) (by simp) with h9675 | h9675
                    · linarith only [h9250, h9675, hlam]
                    · linarith only [h9252, h9675, hlam]
                  · linarith only [h9251, h9674, hlam]
              · linarith only [h3, h9671, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h2, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9681 | h9681
              · rcases p9636_3 (m.d 0 2) (by simp) with h9682 | h9682
                · linarith only [h7337, h9682, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9684 | h9684
                  · rcases p9636_3 (m.d 0 4) (by simp) with h9685 | h9685
                    · rcases p9636_3 (m.d 0 5) (by simp) with h9686 | h9686
                      · linarith only [h9252, h9686, hlam]
                      · linarith only [h8360, h9686, hlam]
                    · linarith only [h7337, h9685, hlam]
                  · linarith only [h4, h9684, hlam]
              · linarith only [h0, h9681, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h9250, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9694 | h9694
              · rcases p9636_3 (m.d 0 2) (by simp) with h9695 | h9695
                · linarith only [h7337, h9695, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9697 | h9697
                  · rcases p9636_3 (m.d 0 4) (by simp) with h9698 | h9698
                    · rcases p9636_3 (m.d 0 5) (by simp) with h9699 | h9699
                      · linarith only [h9252, h9699, hlam]
                      · rcases h2bigk with h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c | h9701c
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h8360, hc12, hc25, hlam, hphi, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h4, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h7337, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h8360, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h0, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9253, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9255, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9257, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9712 | h9712
                          · linarith only [h9712, hlam, p9701_0]
                          · rcases p9701_3 (m.d 1 2) (by simp) with h9714 | h9714
                            · linarith only [h9253, h9714, hlam]
                            · rcases p9701_3 (m.d 2 3) (by simp) with h9716 | h9716
                              · rcases p9701_3 (m.d 2 4) (by simp) with h9717 | h9717
                                · linarith only [h9262, h9717, hlam]
                                · linarith only [h7337, h9717, hlam]
                              · linarith only [h9716, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9721 | h9721
                          · linarith only [h4, h9721, hlam]
                          · linarith only [h0, h9721, hlam]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h7337, hc02, hc23, hlam, hphi, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9727 | h9727
                          · linarith only [h9727, hlam, p9701_0]
                          · rcases p9701_3 (m.d 1 2) (by simp) with h9729 | h9729
                            · linarith only [h9255, h9729, hlam]
                            · rcases p9701_3 (m.d 2 3) (by simp) with h9731 | h9731
                              · rcases p9701_3 (m.d 2 4) (by simp) with h9732 | h9732
                                · rcases p9701_3 (m.d 2 5) (by simp) with h9733 | h9733
                                  · linarith only [h9264, h9733, hlam]
                                  · linarith only [h8360, h9733, hlam]
                                · linarith only [h9732, hlam, p9701_0]
                              · linarith only [h4, h9731, hlam]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9738 | h9738
                          · linarith only [h7337, h9738, hlam]
                          · linarith only [h0, h9738, hlam]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9262, hlam, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9744 | h9744
                          · linarith only [h9744, hlam, p9701_0]
                          · rcases p9701_3 (m.d 1 2) (by simp) with h9746 | h9746
                            · linarith only [h9257, h9746, hlam]
                            · rcases p9701_3 (m.d 2 3) (by simp) with h9748 | h9748
                              · rcases p9701_3 (m.d 2 4) (by simp) with h9749 | h9749
                                · rcases p9701_3 (m.d 2 5) (by simp) with h9750 | h9750
                                  · rcases h3bigk with h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c | h9751c
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h4, h9259, h9261, h9265, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h4, hlam, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      rcases p9751_3 (m.d 0 3) (by simp) with h9755 | h9755
                                      · rcases p9751_3 (m.d 1 3) (by simp) with h9756 | h9756
                                        · linarith only [h1, h9756, hlam]
                                        · linarith only [h9259, h9756, hlam]
                                      · linarith only [h9755, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      rcases p9751_3 (m.d 0 3) (by simp) with h9760 | h9760
                                      · rcases p9751_3 (m.d 1 3) (by simp) with h9761 | h9761
                                        · linarith only [h1, h9761, hlam]
                                        · linarith only [h9260, h9761, hlam]
                                      · linarith only [h9760, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h1, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9253, hlam, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h1, h9265, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      rcases p9751_3 (m.d 0 3) (by simp) with h9773 | h9773
                                      · linarith only [h4, h9773, hlam]
                                      · linarith only [h9250, h9773, hlam]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      rcases p9751_3 (m.d 0 3) (by simp) with h9776 | h9776
                                      · linarith only [h4, h9776, hlam]
                                      · linarith only [h9251, h9776, hlam]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9250, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9259, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9262, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9265, hlam, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9251, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9260, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9263, hlam, p9751_0]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [h9251, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9751_1]
                                    · have p9751_0 := h9751c.1
                                      have p9751_1 := h9751c.2.1
                                      have p9751_2 := h9751c.2.2.1
                                      have p9751_3 := h9751c.2.2.2
                                      linarith only [hlam, p9751_0]
                                  · linarith only [h9750, hlam, p9701_0]
                                · linarith only [h7337, h9749, hlam]
                              · linarith only [h4, h9748, hlam]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          rcases p9701_3 (m.d 0 2) (by simp) with h9792 | h9792
                          · linarith only [h8360, h9792, hlam]
                          · linarith only [h0, h9792, hlam]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9263, hlam, p9701_1]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [h9264, hlam, p9701_0]
                        · have p9701_0 := h9701c.1
                          have p9701_1 := h9701c.2.1
                          have p9701_2 := h9701c.2.2.1
                          have p9701_3 := h9701c.2.2.2
                          linarith only [hlam, p9701_0]
                    · linarith only [h9252, h9698, hlam]
                  · linarith only [h9251, h9697, hlam]
              · linarith only [h3, h9694, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h3, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              rcases p9636_3 (m.d 0 1) (by simp) with h9802 | h9802
              · rcases p9636_3 (m.d 0 2) (by simp) with h9803 | h9803
                · linarith only [h8360, h9803, hlam]
                · rcases p9636_3 (m.d 0 3) (by simp) with h9805 | h9805
                  · rcases p9636_3 (m.d 0 4) (by simp) with h9806 | h9806
                    · rcases p9636_3 (m.d 0 5) (by simp) with h9807 | h9807
                      · rcases h2bigk with h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c | h9808c
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9636_1, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h4, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h7337, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h8360, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h0, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9253, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9255, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9257, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9819 | h9819
                          · linarith only [h9819, hlam, p9808_0]
                          · rcases p9808_3 (m.d 1 2) (by simp) with h9821 | h9821
                            · linarith only [h9253, h9821, hlam]
                            · rcases p9808_3 (m.d 2 3) (by simp) with h9823 | h9823
                              · rcases p9808_3 (m.d 2 4) (by simp) with h9824 | h9824
                                · linarith only [h9262, h9824, hlam]
                                · linarith only [h7337, h9824, hlam]
                              · linarith only [h9823, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9828 | h9828
                          · linarith only [h4, h9828, hlam]
                          · linarith only [h0, h9828, hlam]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h7337, h9252, hc02, hc23, hlam, hphi, p9636_1, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9834 | h9834
                          · linarith only [h9834, hlam, p9808_0]
                          · rcases p9808_3 (m.d 1 2) (by simp) with h9836 | h9836
                            · linarith only [h9255, h9836, hlam]
                            · rcases p9808_3 (m.d 2 3) (by simp) with h9838 | h9838
                              · rcases p9808_3 (m.d 2 4) (by simp) with h9839 | h9839
                                · rcases p9808_3 (m.d 2 5) (by simp) with h9840 | h9840
                                  · linarith only [h9264, h9840, hlam]
                                  · linarith only [h8360, h9840, hlam]
                                · linarith only [h9839, hlam, p9808_0]
                              · linarith only [h4, h9838, hlam]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9845 | h9845
                          · linarith only [h7337, h9845, hlam]
                          · linarith only [h0, h9845, hlam]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9262, hlam, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9636_1, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9851 | h9851
                          · linarith only [h9851, hlam, p9808_0]
                          · rcases p9808_3 (m.d 1 2) (by simp) with h9853 | h9853
                            · linarith only [h9257, h9853, hlam]
                            · rcases p9808_3 (m.d 2 3) (by simp) with h9855 | h9855
                              · rcases p9808_3 (m.d 2 4) (by simp) with h9856 | h9856
                                · rcases p9808_3 (m.d 2 5) (by simp) with h9857 | h9857
                                  · rcases h3bigk with h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c | h9858c
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h4, h9259, h9261, h9265, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h4, hlam, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      rcases p9858_3 (m.d 0 3) (by simp) with h9862 | h9862
                                      · rcases p9858_3 (m.d 1 3) (by simp) with h9863 | h9863
                                        · linarith only [h1, h9863, hlam]
                                        · linarith only [h9259, h9863, hlam]
                                      · linarith only [h9862, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      rcases p9858_3 (m.d 0 3) (by simp) with h9867 | h9867
                                      · rcases p9858_3 (m.d 1 3) (by simp) with h9868 | h9868
                                        · linarith only [h1, h9868, hlam]
                                        · linarith only [h9260, h9868, hlam]
                                      · linarith only [h9867, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h1, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9253, hlam, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      rcases p9858_3 (m.d 0 3) (by simp) with h9880 | h9880
                                      · linarith only [h4, h9880, hlam]
                                      · linarith only [h9250, h9880, hlam]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      rcases p9858_3 (m.d 0 3) (by simp) with h9883 | h9883
                                      · linarith only [h4, h9883, hlam]
                                      · linarith only [h9251, h9883, hlam]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9250, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9259, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9262, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9265, hlam, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9251, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9260, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9263, hlam, p9858_0]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [h9251, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p9858_1]
                                    · have p9858_0 := h9858c.1
                                      have p9858_1 := h9858c.2.1
                                      have p9858_2 := h9858c.2.2.1
                                      have p9858_3 := h9858c.2.2.2
                                      linarith only [hlam, p9858_0]
                                  · linarith only [h9857, hlam, p9808_0]
                                · linarith only [h7337, h9856, hlam]
                              · linarith only [h4, h9855, hlam]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          rcases p9808_3 (m.d 0 2) (by simp) with h9899 | h9899
                          · linarith only [h8360, h9899, hlam]
                          · linarith only [h0, h9899, hlam]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9263, hlam, p9808_1]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [h9264, hlam, p9808_0]
                        · have p9808_0 := h9808c.1
                          have p9808_1 := h9808c.2.1
                          have p9808_2 := h9808c.2.2.1
                          have p9808_3 := h9808c.2.2.2
                          linarith only [hlam, p9808_0]
                      · linarith only [h8360, h9807, hlam]
                    · linarith only [h7337, h9806, hlam]
                  · linarith only [h4, h9805, hlam]
              · linarith only [h0, h9802, hlam]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h9251, hlam, p9636_0]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [h9252, hlam, p9636_1]
            · have p9636_0 := h9636c.1
              have p9636_1 := h9636c.2.1
              have p9636_2 := h9636c.2.2.1
              have p9636_3 := h9636c.2.2.2
              linarith only [hlam, p9636_0]
        · linarith only [h0, h1, h7337, h9259, h9261, h9264, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · linarith only [h4, h9251, h9263, hlam]
    · linarith only [h4, h9250, h9262, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h9915 | h9915
    · rcases m.htr 2 3 5 (by decide) (by decide) with h9916 | h9916
      · rcases m.htr 2 4 5 (by decide) (by decide) with h9917 | h9917
        · rcases m.htr 3 4 5 (by decide) (by decide) with h9918 | h9918
          · linarith only [h9259, h9261, h9918, hlam]
          · rcases h0bigk with h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c | h9920c
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              rcases p9920_3 (m.d 0 1) (by simp) with h9922 | h9922
              · rcases p9920_3 (m.d 0 2) (by simp) with h9923 | h9923
                · linarith only [h0, h9923, hlam]
                · rcases p9920_3 (m.d 0 3) (by simp) with h9925 | h9925
                  · linarith only [h1, h9925, hlam]
                  · linarith only [h4, h9925, hlam]
              · linarith only [h0, h9922, hlam]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9250, h9252, h9255, h9261, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9252, h9255, h9261, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              rcases p9920_3 (m.d 0 1) (by simp) with h9931 | h9931
              · rcases p9920_3 (m.d 0 2) (by simp) with h9932 | h9932
                · linarith only [h0, h9932, hlam]
                · rcases p9920_3 (m.d 0 3) (by simp) with h9934 | h9934
                  · linarith only [h1, h9934, hlam]
                  · linarith only [h9251, h9934, hlam]
              · linarith only [h3, h9931, hlam]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h0, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h4, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h7337, hlam, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h8360, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h1, hlam, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              rcases p9920_3 (m.d 0 1) (by simp) with h9944 | h9944
              · rcases p9920_3 (m.d 0 2) (by simp) with h9945 | h9945
                · linarith only [h4, h9945, hlam]
                · rcases p9920_3 (m.d 0 3) (by simp) with h9947 | h9947
                  · rcases p9920_3 (m.d 0 4) (by simp) with h9948 | h9948
                    · linarith only [h9250, h9948, hlam]
                    · linarith only [h7337, h9948, hlam]
                  · linarith only [h4, h9947, hlam]
              · linarith only [h0, h9944, hlam]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9252, h9255, h9261, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h4, h9252, h9255, h9261, hc12, hc23, hlam, hphi, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h2, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              rcases p9920_3 (m.d 0 1) (by simp) with h9957 | h9957
              · rcases p9920_3 (m.d 0 2) (by simp) with h9958 | h9958
                · linarith only [h7337, h9958, hlam]
                · rcases p9920_3 (m.d 0 3) (by simp) with h9960 | h9960
                  · rcases p9920_3 (m.d 0 4) (by simp) with h9961 | h9961
                    · rcases p9920_3 (m.d 0 5) (by simp) with h9962 | h9962
                      · linarith only [h9252, h9962, hlam]
                      · linarith only [h8360, h9962, hlam]
                    · linarith only [h7337, h9961, hlam]
                  · linarith only [h4, h9960, hlam]
              · linarith only [h0, h9957, hlam]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9250, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h7337, h9252, h9255, h9261, h9915, hc12, hc23, hlam, hphi, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h3, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              rcases p9920_3 (m.d 0 1) (by simp) with h9972 | h9972
              · rcases p9920_3 (m.d 0 2) (by simp) with h9973 | h9973
                · linarith only [h8360, h9973, hlam]
                · rcases p9920_3 (m.d 0 3) (by simp) with h9975 | h9975
                  · rcases p9920_3 (m.d 0 4) (by simp) with h9976 | h9976
                    · rcases p9920_3 (m.d 0 5) (by simp) with h9977 | h9977
                      · rcases h2bigk with h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c | h9978c
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p9920_1, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h4, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h7337, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h8360, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h0, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9253, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9255, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9257, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h9989 | h9989
                          · linarith only [h9989, hlam, p9978_0]
                          · rcases p9978_3 (m.d 1 2) (by simp) with h9991 | h9991
                            · linarith only [h9253, h9991, hlam]
                            · rcases p9978_3 (m.d 2 3) (by simp) with h9993 | h9993
                              · rcases p9978_3 (m.d 2 4) (by simp) with h9994 | h9994
                                · linarith only [h9915, h9994, hlam]
                                · linarith only [h7337, h9994, hlam]
                              · linarith only [h9993, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h9998 | h9998
                          · linarith only [h4, h9998, hlam]
                          · linarith only [h0, h9998, hlam]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h7337, h9252, hc02, hc23, hlam, hphi, p9920_1, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h0, h8360, hc12, hc23, hlam, hphi, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h10004 | h10004
                          · linarith only [h10004, hlam, p9978_0]
                          · rcases p9978_3 (m.d 1 2) (by simp) with h10006 | h10006
                            · linarith only [h10006, h9255, hlam]
                            · rcases p9978_3 (m.d 2 3) (by simp) with h10008 | h10008
                              · rcases p9978_3 (m.d 2 4) (by simp) with h10009 | h10009
                                · rcases p9978_3 (m.d 2 5) (by simp) with h10010 | h10010
                                  · linarith only [h10010, h9917, hlam]
                                  · linarith only [h10010, h8360, hlam]
                                · linarith only [h10009, hlam, p9978_0]
                              · linarith only [h10008, h4, hlam]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h10015 | h10015
                          · linarith only [h10015, h7337, hlam]
                          · linarith only [h0, h10015, hlam]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9915, hlam, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h0, h8360, hc12, hc24, hlam, hphi, p9920_1, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h10021 | h10021
                          · linarith only [h10021, hlam, p9978_0]
                          · rcases p9978_3 (m.d 1 2) (by simp) with h10023 | h10023
                            · linarith only [h10023, h9257, hlam]
                            · rcases p9978_3 (m.d 2 3) (by simp) with h10025 | h10025
                              · rcases p9978_3 (m.d 2 4) (by simp) with h10026 | h10026
                                · rcases p9978_3 (m.d 2 5) (by simp) with h10027 | h10027
                                  · rcases h3bigk with h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c | h10028c
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h4, h9253, hc12, hc23, hlam, hphi, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h4, hlam, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      rcases p10028_3 (m.d 0 3) (by simp) with h10032 | h10032
                                      · rcases p10028_3 (m.d 1 3) (by simp) with h10033 | h10033
                                        · linarith only [h1, h10033, hlam]
                                        · linarith only [h10033, h9259, hlam]
                                      · linarith only [h10032, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      rcases p10028_3 (m.d 0 3) (by simp) with h10037 | h10037
                                      · rcases p10028_3 (m.d 1 3) (by simp) with h10038 | h10038
                                        · linarith only [h1, h10038, hlam]
                                        · linarith only [h10038, h9260, hlam]
                                      · linarith only [h10037, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h1, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9253, hlam, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h1, h9918, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9253, hc12, hc23, hlam, hphi, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      rcases p10028_3 (m.d 0 3) (by simp) with h10050 | h10050
                                      · linarith only [h10050, h4, hlam]
                                      · linarith only [h10050, h9250, hlam]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      rcases p10028_3 (m.d 0 3) (by simp) with h10053 | h10053
                                      · linarith only [h10053, h4, hlam]
                                      · linarith only [h10053, h9251, hlam]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9250, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9259, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9915, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9918, hlam, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9251, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9260, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h9916, hlam, p10028_0]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [h4, h9251, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10028_1]
                                    · have p10028_0 := h10028c.1
                                      have p10028_1 := h10028c.2.1
                                      have p10028_2 := h10028c.2.2.1
                                      have p10028_3 := h10028c.2.2.2
                                      linarith only [hlam, p10028_0]
                                  · linarith only [h10027, hlam, p9978_0]
                                · linarith only [h10026, h7337, hlam]
                              · linarith only [h10025, h4, hlam]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          rcases p9978_3 (m.d 0 2) (by simp) with h10069 | h10069
                          · linarith only [h10069, h8360, hlam]
                          · linarith only [h0, h10069, hlam]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9916, hlam, p9978_1]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [h9917, hlam, p9978_0]
                        · have p9978_0 := h9978c.1
                          have p9978_1 := h9978c.2.1
                          have p9978_2 := h9978c.2.2.1
                          have p9978_3 := h9978c.2.2.2
                          linarith only [hlam, p9978_0]
                      · linarith only [h8360, h9977, hlam]
                    · linarith only [h7337, h9976, hlam]
                  · linarith only [h4, h9975, hlam]
              · linarith only [h0, h9972, hlam]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9251, hlam, p9920_0]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [h9252, hlam, p9920_1]
            · have p9920_0 := h9920c.1
              have p9920_1 := h9920c.2.1
              have p9920_2 := h9920c.2.2.1
              have p9920_3 := h9920c.2.2.2
              linarith only [hlam, p9920_0]
        · linarith only [h0, h4, h7337, h9250, h9252, h9917, hc12, hc23, hlam, hphi]
      · linarith only [h4, h9250, h9252, h9260, h9261, h9916, hlam]
    · linarith only [h4, h9250, h9915, hlam]

end R2N4
