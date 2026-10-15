import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7184000 in
set_option maxHeartbeats 7184000 in
theorem r1l7_21_14_H_I_L_I_s5_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5235 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5236 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5237 | h5237
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5238 | h5238
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5239 | h5239
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5240 | h5240
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5241 | h5241
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5242 | h5242
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5243 | h5243
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5244 | h5244
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5245 | h5245
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5246 | h5246
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5247 | h5247
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5248 | h5248
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5249 | h5249
                          · linarith only [h0, h5235, h5241, h5247, h5249, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h5235, h5244, h5246, h5249, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h5235, h5244, h5246, h5248, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h5235, h5244, h5247, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5254 | h5254
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5255 | h5255
                        · linarith only [h5242, h5246, h5255, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5257 | h5257
                          · linarith only [h5242, h5246, h5254, h5257, hlam]
                          · rcases h1bigk with h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c | h5259c
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5245, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              rcases p5259_3 (m.d 0 1) (by simp) with h5268 | h5268
                              · linarith only [h0, h5268, hlam]
                              · linarith only [h5236, h5268, hlam]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              rcases p5259_3 (m.d 0 1) (by simp) with h5271 | h5271
                              · linarith only [h0, h5271, hlam]
                              · linarith only [h5237, h5271, hlam]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5235, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5241, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5235, h5242, h5254, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, h5235, h5242, h5246, h5254, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5236, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5242, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5244, hlam, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5246, hlam, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5237, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5243, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h5245, hlam, p5259_0]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [h0, h5237, h5242, h5254, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5259_1]
                            · have p5259_0 := h5259c.1
                              have p5259_1 := h5259c.2.1
                              have p5259_2 := h5259c.2.2.1
                              have p5259_3 := h5259c.2.2.2
                              linarith only [hlam, p5259_0]
                      · linarith only [h0, h5235, h5244, h5254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5290 | h5290
                    · linarith only [h5244, h5245, h5290, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5292 | h5292
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5293 | h5293
                        · linarith only [h5242, h5290, h5293, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5295 | h5295
                          · linarith only [h5241, h5245, h5290, h5292, h5295, hlam]
                          · linarith only [h0, h5235, h5239, h5240, h5241, h5245, h5292, h5295, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h5244, h5245, h5292, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5299 | h5299
                  · linarith only [h0, h5235, h5239, h5244, h5299, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5301 | h5301
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5302 | h5302
                      · linarith only [h5241, h5244, h5302, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5304 | h5304
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5305 | h5305
                          · rcases h1bigk with h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c | h5306c
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              rcases p5306_3 (m.d 0 1) (by simp) with h5314 | h5314
                              · linarith only [h0, h5314, hlam]
                              · linarith only [h5235, h5314, hlam]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5242, h5304, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              rcases p5306_3 (m.d 0 1) (by simp) with h5318 | h5318
                              · linarith only [h0, h5318, hlam]
                              · linarith only [h5237, h5318, hlam]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5235, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5241, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5244, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5299, hlam, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5236, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5242, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5236, h5241, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, h5235, h5239, h5241, h5244, h5299, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5237, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5243, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h0, h5237, h5241, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5306_1]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [h5301, hlam, p5306_0]
                            · have p5306_0 := h5306c.1
                              have p5306_1 := h5306c.2.1
                              have p5306_2 := h5306c.2.2.1
                              have p5306_3 := h5306c.2.2.2
                              linarith only [hlam, p5306_0]
                          · linarith only [h5242, h5244, h5304, h5305, hlam]
                        · linarith only [h0, h5236, h5301, h5304, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5338 | h5338
                      · linarith only [h5241, h5244, h5338, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5340 | h5340
                        · linarith only [h5242, h5301, h5340, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5342 | h5342
                          · linarith only [h0, h5235, h5239, h5244, h5301, h5342, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h5235, h5239, h5240, h5241, h5244, h5342, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h5237, h5243, hlam]
            · linarith only [h0, h5238, h5242, hlam]
          · linarith only [h0, h5235, h5241, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5348 | h5348
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5349 | h5349
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5350 | h5350
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5351 | h5351
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5352 | h5352
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5353 | h5353
                    · linarith only [h0, h5236, h5240, h5353, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5355 | h5355
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5356 | h5356
                        · linarith only [h5236, h5240, h5349, h5356, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5358 | h5358
                          · linarith only [h5236, h5240, h5349, h5355, h5358, hlam]
                          · rcases h1bigk with h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c | h5360c
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, h5348, h5355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, h5349, h5355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5348, h5355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              rcases p5360_3 (m.d 0 1) (by simp) with h5369 | h5369
                              · linarith only [h0, h5369, hlam]
                              · linarith only [h5236, h5369, hlam]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              rcases p5360_3 (m.d 0 1) (by simp) with h5372 | h5372
                              · linarith only [h0, h5372, hlam]
                              · linarith only [h5237, h5372, hlam]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5235, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5348, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5235, h5349, h5355, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, h5235, h5349, h5353, h5355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5236, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5349, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5351, hlam, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5353, hlam, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5237, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5350, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h5352, hlam, p5360_0]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [h0, h5237, h5349, h5355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5360_1]
                            · have p5360_0 := h5360c.1
                              have p5360_1 := h5360c.2.1
                              have p5360_2 := h5360c.2.2.1
                              have p5360_3 := h5360c.2.2.2
                              linarith only [hlam, p5360_0]
                      · linarith only [h0, h5235, h5351, h5355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5391 | h5391
                    · linarith only [h0, h5236, h5237, h5240, h5351, h5352, h5391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5393 | h5393
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5394 | h5394
                        · linarith only [h5238, h5240, h5394, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5396 | h5396
                          · linarith only [h5239, h5240, h5396, hlam]
                          · rcases h1bigk with h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c | h5398c
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h0, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5348, h5393, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              rcases p5398_3 (m.d 0 1) (by simp) with h5407 | h5407
                              · linarith only [h0, h5407, hlam]
                              · linarith only [h5236, h5407, hlam]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5348, h5352, h5393, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5235, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5348, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5237, h5349, h5352, h5393, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5352, hlam, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5236, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5349, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5351, hlam, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5391, hlam, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5237, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5350, hlam, p5398_0]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h5237, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [h0, h5237, h5349, h5393, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5398_1]
                            · have p5398_0 := h5398c.1
                              have p5398_1 := h5398c.2.1
                              have p5398_2 := h5398c.2.2.1
                              have p5398_3 := h5398c.2.2.2
                              linarith only [hlam, p5398_0]
                      · linarith only [h5351, h5352, h5393, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5427 | h5427
                  · linarith only [h0, h5235, h5239, h5351, h5427, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5429 | h5429
                    · linarith only [h0, h5236, h5239, h5240, h5348, h5351, h5429, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5431 | h5431
                      · linarith only [h5348, h5351, h5431, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5433 | h5433
                        · linarith only [h0, h5238, h5239, h5240, h5348, h5351, h5433, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5435 | h5435
                          · linarith only [h5239, h5240, h5435, hlam]
                          · rcases h1bigk with h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c | h5437c
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, h5348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              rcases p5437_3 (m.d 0 1) (by simp) with h5445 | h5445
                              · linarith only [h0, h5445, hlam]
                              · linarith only [h5235, h5445, hlam]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              rcases p5437_3 (m.d 0 1) (by simp) with h5448 | h5448
                              · linarith only [h0, h5448, hlam]
                              · linarith only [h5236, h5448, hlam]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              rcases p5437_3 (m.d 0 1) (by simp) with h5451 | h5451
                              · linarith only [h0, h5451, hlam]
                              · linarith only [h5237, h5451, hlam]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5235, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5348, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5351, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5427, hlam, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5236, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5349, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5236, h5348, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5429, hlam, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5237, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h5350, hlam, p5437_0]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, h5237, h5348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [h0, h5237, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5437_1]
                            · have p5437_0 := h5437c.1
                              have p5437_1 := h5437c.2.1
                              have p5437_2 := h5437c.2.2.1
                              have p5437_3 := h5437c.2.2.2
                              linarith only [hlam, p5437_0]
              · linarith only [h0, h5237, h5350, hlam]
            · linarith only [h0, h5238, h5349, hlam]
          · linarith only [h0, h5235, h5348, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5472 | h5472
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5473 | h5473
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5474 | h5474
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5475 | h5475
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5476 | h5476
                · linarith only [h5235, h5239, h5476, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5478 | h5478
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5479 | h5479
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5480 | h5480
                      · linarith only [h5235, h5239, h5473, h5480, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5482 | h5482
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5483 | h5483
                          · rcases h1bigk with h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c | h5484c
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h0, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5478, h5483, hc01, hc45, hlam, hphi, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5478, h5483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5474, h5482, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              rcases p5484_3 (m.d 0 1) (by simp) with h5494 | h5494
                              · linarith only [h0, h5494, hlam]
                              · linarith only [h5237, h5494, hlam]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5235, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5473, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5476, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5236, h5476, h5478, h5483, hc01, hc45, hlam, hphi, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5236, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5474, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5236, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h0, h5236, h5478, h5483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5484_1]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5237, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5475, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5478, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [h5479, hlam, p5484_0]
                            · have p5484_0 := h5484c.1
                              have p5484_1 := h5484c.2.1
                              have p5484_2 := h5484c.2.2.1
                              have p5484_3 := h5484c.2.2.2
                              linarith only [hlam, p5484_0]
                          · linarith only [h5235, h5239, h5478, h5482, h5483, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h5236, h5479, h5482, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h5236, h5472, h5476, h5478, h5479, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5515 | h5515
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5516 | h5516
                      · linarith only [h5235, h5239, h5473, h5516, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5518 | h5518
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5519 | h5519
                          · rcases h1bigk with h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c | h5520c
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, h5478, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5528 | h5528
                              · linarith only [h0, h5528, hlam]
                              · linarith only [h5235, h5528, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5474, h5518, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              rcases p5520_3 (m.d 0 1) (by simp) with h5532 | h5532
                              · linarith only [h0, h5532, hlam]
                              · linarith only [h5237, h5532, hlam]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5235, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5473, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5476, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5478, hlam, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5236, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5474, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5236, h5473, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5236, h5239, h5473, h5478, hc23, hc34, hlam, hphi, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5237, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5475, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h0, h5237, h5473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5520_1]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [h5515, hlam, p5520_0]
                            · have p5520_0 := h5520c.1
                              have p5520_1 := h5520c.2.1
                              have p5520_2 := h5520c.2.2.1
                              have p5520_3 := h5520c.2.2.2
                              linarith only [hlam, p5520_0]
                          · linarith only [h0, h5235, h5238, h5239, h5473, h5518, h5519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h5236, h5515, h5518, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5552 | h5552
                      · linarith only [h0, h5235, h5239, h5472, h5473, h5515, h5552, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5554 | h5554
                        · linarith only [h5474, h5515, h5554, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5556 | h5556
                          · rcases h1bigk with h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c | h5557c
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, h5473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, h5473, h5476, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, h5473, h5476, h5515, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              rcases p5557_3 (m.d 0 1) (by simp) with h5565 | h5565
                              · linarith only [h0, h5565, hlam]
                              · linarith only [h5235, h5565, hlam]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              rcases p5557_3 (m.d 0 1) (by simp) with h5568 | h5568
                              · linarith only [h0, h5568, hlam]
                              · linarith only [h5236, h5568, hlam]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              rcases p5557_3 (m.d 0 1) (by simp) with h5571 | h5571
                              · linarith only [h0, h5571, hlam]
                              · linarith only [h5237, h5571, hlam]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5235, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5473, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5476, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5478, hlam, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5236, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5474, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5236, h5472, h5473, h5515, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5515, hlam, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5237, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h5475, hlam, p5557_0]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, h5237, h5473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [h0, h5236, h5472, h5515, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5557_1]
                            · have p5557_0 := h5557c.1
                              have p5557_1 := h5557c.2.1
                              have p5557_2 := h5557c.2.2.1
                              have p5557_3 := h5557c.2.2.2
                              linarith only [hlam, p5557_0]
                          · linarith only [h5239, h5472, h5556, hlam]
              · linarith only [h0, h5237, h5475, hlam]
            · linarith only [h0, h5238, h5474, hlam]
          · linarith only [h0, h5235, h5473, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5593 | h5593
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5594 | h5594
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5595 | h5595
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5596 | h5596
                · linarith only [h0, h5235, h5239, h5596, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5598 | h5598
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5599 | h5599
                    · linarith only [h5236, h5472, h5599, hlam]
                    · linarith only [h5596, h5598, h5599, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5602 | h5602
                    · linarith only [h5236, h5472, h5602, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5604 | h5604
                      · linarith only [h5235, h5239, h5593, h5604, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5606 | h5606
                        · linarith only [h5238, h5472, h5606, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5608 | h5608
                          · rcases h1bigk with h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c | h5609c
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h0, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h0, h5593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h0, h5593, h5596, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              rcases p5609_3 (m.d 0 1) (by simp) with h5617 | h5617
                              · linarith only [h0, h5617, hlam]
                              · linarith only [h5235, h5617, hlam]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              rcases p5609_3 (m.d 0 1) (by simp) with h5620 | h5620
                              · linarith only [h0, h5620, hlam]
                              · linarith only [h5236, h5620, hlam]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              rcases p5609_3 (m.d 0 1) (by simp) with h5623 | h5623
                              · linarith only [h0, h5623, hlam]
                              · linarith only [h5237, h5623, hlam]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5235, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5593, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5596, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5598, hlam, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5236, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5594, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5236, h5472, h5593, h5608, hc23, hc34, hlam, hphi, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5602, hlam, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5237, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5595, hlam, p5609_0]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h5237, h5593, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [h0, h5237, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5609_1]
                            · have p5609_0 := h5609c.1
                              have p5609_1 := h5609c.2.1
                              have p5609_2 := h5609c.2.2.1
                              have p5609_3 := h5609c.2.2.2
                              linarith only [hlam, p5609_0]
                          · rcases h1bigk with h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c | h5641c
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h5593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h5594, h5604, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              rcases p5641_3 (m.d 0 1) (by simp) with h5649 | h5649
                              · linarith only [h0, h5649, hlam]
                              · linarith only [h5235, h5649, hlam]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              rcases p5641_3 (m.d 0 1) (by simp) with h5652 | h5652
                              · linarith only [h0, h5652, hlam]
                              · linarith only [h5236, h5652, hlam]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              rcases p5641_3 (m.d 0 1) (by simp) with h5655 | h5655
                              · linarith only [h0, h5655, hlam]
                              · linarith only [h5237, h5655, hlam]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5235, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5593, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5596, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5598, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5236, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5594, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5236, h5593, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5602, hlam, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5237, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h5595, hlam, p5641_0]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h5237, h5593, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [h0, h5237, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5641_1]
                            · have p5641_0 := h5641c.1
                              have p5641_1 := h5641c.2.1
                              have p5641_2 := h5641c.2.2.1
                              have p5641_3 := h5641c.2.2.2
                              linarith only [hlam, p5641_0]
              · linarith only [h0, h5237, h5595, hlam]
            · linarith only [h0, h5238, h5594, hlam]
          · linarith only [h0, h5235, h5593, hlam]
    · linarith only [h0, h5236, h5238, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5677 | h5677
    · rcases m.htr 0 3 4 (by decide) (by decide) with h5678 | h5678
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5679 | h5679
        · linarith only [h5235, h5237, h5678, h5679, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5681 | h5681
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5682 | h5682
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5683 | h5683
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5684 | h5684
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5685 | h5685
                  · linarith only [h5235, h5237, h5685, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5687 | h5687
                    · linarith only [h5236, h5237, h5679, h5685, h5687, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h5235, h5237, h5684, h5687, hc34, hc45, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5690 | h5690
                  · linarith only [h5235, h5237, h5678, h5683, h5684, h5690, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h5235, h5237, h5678, h5681, h5684, h5690, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5693 | h5693
                · linarith only [h0, h5235, h5683, h5693, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h5235, h5678, h5683, h5693, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h0, h5677, h5682, hlam]
          · linarith only [h0, h5235, h5681, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5698 | h5698
        · linarith only [h5236, h5237, h5698, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5700 | h5700
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5701 | h5701
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5702 | h5702
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5703 | h5703
                · linarith only [h5235, h5678, h5703, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5705 | h5705
                  · linarith only [h5236, h5237, h5703, h5705, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5707 | h5707
                    · linarith only [h5236, h5237, h5698, h5702, h5707, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5709 | h5709
                      · linarith only [h5235, h5678, h5700, h5709, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5711 | h5711
                        · linarith only [h5236, h5237, h5677, h5703, h5707, h5711, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5713 | h5713
                          · linarith only [h5236, h5237, h5700, h5703, h5707, h5713, hc23, hc34, hlam, hphi]
                          · rcases h1bigk with h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c | h5715c
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h0, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5237, h5700, h5702, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5237, h5700, h5702, h5703, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5237, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              rcases p5715_3 (m.d 0 1) (by simp) with h5723 | h5723
                              · linarith only [h0, h5723, hlam]
                              · linarith only [h5235, h5723, hlam]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              rcases p5715_3 (m.d 0 1) (by simp) with h5726 | h5726
                              · linarith only [h0, h5726, hlam]
                              · linarith only [h5236, h5726, hlam]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5236, h5237, h5700, h5703, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5235, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5700, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5703, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5705, hlam, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5236, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5701, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5236, h5700, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5707, hlam, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5702, hlam, p5715_0]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5700, h5705, h5713, hc23, hc45, hlam, hphi, ht34, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [h5700, h5703, h5705, h5713, hc23, hc45, hlam, hphi, ht34, p5715_1]
                            · have p5715_0 := h5715c.1
                              have p5715_1 := h5715c.2.1
                              have p5715_2 := h5715c.2.2.1
                              have p5715_3 := h5715c.2.2.2
                              linarith only [hlam, p5715_0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5745 | h5745
                · linarith only [h0, h5235, h5702, h5745, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5747 | h5747
                  · linarith only [h0, h5236, h5702, h5745, h5747, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5749 | h5749
                    · linarith only [h0, h5236, h5702, h5749, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5751 | h5751
                      · linarith only [h5678, h5700, h5702, h5751, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5753 | h5753
                        · linarith only [h5235, h5237, h5677, h5700, h5749, h5753, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h5236, h5700, h5702, h5745, h5753, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h5677, h5701, hlam]
          · linarith only [h0, h5235, h5700, hlam]
    · linarith only [h0, h5236, h5677, hlam]

end R2N4
