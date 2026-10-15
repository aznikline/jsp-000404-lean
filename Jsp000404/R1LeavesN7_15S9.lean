import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_15S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11006000 in
set_option maxHeartbeats 11006000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s2 m hb0 hb1 hb3 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h5214 | h5214
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5215 | h5215
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5216 | h5216
        · linarith only [h0, h2, h5216, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5218 | h5218
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5219 | h5219
            · linarith only [h1, h2, h5219, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5221 | h5221
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5222 | h5222
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5223 | h5223
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5224 | h5224
                    · linarith only [h0, h2, h5216, h5218, h5224, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5226 | h5226
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5227 | h5227
                        · linarith only [h1, h2, h5219, h5224, h5227, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h5223, h5227, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5218, h5223, h5224, h5226, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5215, h5216, h5223, hc12, hc24, hlam, hphi]
                · linarith only [h2, h5214, h5222, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5233 | h5233
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5234 | h5234
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5235 | h5235
                    · linarith only [h0, h2, h5216, h5235, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5237 | h5237
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5238 | h5238
                        · linarith only [h1, h5219, h5238, hlam]
                        · linarith only [h0, h2, h5234, h5238, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5218, h5234, h5237, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h5215, h5216, h5234, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h5218, h5233, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5244 | h5244
            · linarith only [h1, h2, h5244, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5246 | h5246
              · linarith only [h5215, h5218, h5246, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5248 | h5248
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5249 | h5249
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5250 | h5250
                    · linarith only [h0, h2, h5216, h5250, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5252 | h5252
                      · linarith only [h0, h5218, h5252, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5254 | h5254
                        · linarith only [h0, h2, h5244, h5249, h5254, hlam]
                        · linarith only [h2, h5214, h5249, h5252, h5254, hc23, hc34, hlam, hphi]
                  · linarith only [h5215, h5218, h5249, hc12, hc25, hlam, hphi]
                · linarith only [h2, h5214, h5248, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5259 | h5259
        · linarith only [h0, h2, h5259, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5261 | h5261
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5262 | h5262
            · linarith only [h1, h2, h5262, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5264 | h5264
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5265 | h5265
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5266 | h5266
                  · linarith only [h0, h2, h5215, h5266, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5268 | h5268
                    · linarith only [h0, h2, h5259, h5268, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5270 | h5270
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5271 | h5271
                        · linarith only [h1, h5262, h5264, h5271, hc01, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5273 | h5273
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5274 | h5274
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5275 | h5275
                              · linarith only [h1, h2, h5266, h5270, h5271, h5275, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5277 | h5277
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5278 | h5278
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5279 | h5279
                                    · rcases h0bigk with h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h2, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h2, h5215, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h2, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h2, h5214, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5215, hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5259, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h2, h5214, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h1, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h5270, h5277, h5279, hc03, hc45, hlam, hphi, ht0b, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5262, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h1, h2, h5214, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h5270, h5277, h5279, hc04, hc45, hlam, hphi, ht0b, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h0, h2, h5268, h5270, h5275, h5277, h5279, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h2, h5268, h5275, hc03, hc34, hlam, hphi, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        rcases p5280_3 (m.d 0 1) (by simp) with h5300 | h5300
                                        · linarith only [h2, h5300, hlam]
                                        · linarith only [h5214, h5300, hlam]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5214, hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5261, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5264, hlam, p5280_0]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [h5265, hlam, p5280_1]
                                      · have p5280_0 := h5280c.1
                                        have p5280_1 := h5280c.2.1
                                        have p5280_2 := h5280c.2.2.1
                                        have p5280_3 := h5280c.2.2.2
                                        linarith only [hlam, p5280_0]
                                    · linarith only [h1, h2, h5266, h5268, h5275, h5279, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h5214, h5266, h5268, h5270, h5274, h5277, h5278, hc05, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h5215, h5264, h5270, h5277, hc03, hc25, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1, h2, h5266, h5270, h5274, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h2, h5264, h5266, h5270, h5273, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1, h2, h5215, h5261, h5268, h5270, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h5215, h5261, h5265, hlam]
              · linarith only [h5215, h5261, h5264, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5316 | h5316
            · linarith only [h1, h2, h5316, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5318 | h5318
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5319 | h5319
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5320 | h5320
                  · linarith only [h0, h2, h5215, h5320, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5322 | h5322
                    · linarith only [h0, h5259, h5322, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5324 | h5324
                      · linarith only [h0, h5261, h5324, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5326 | h5326
                        · linarith only [h1, h2, h5316, h5322, h5326, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5328 | h5328
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5329 | h5329
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5330 | h5330
                              · linarith only [h0, h2, h5326, h5330, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5332 | h5332
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5333 | h5333
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5334 | h5334
                                    · rcases h0bigk with h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c | h5335c
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h2, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h2, hlam, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h2, h5322, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h0, hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5215, hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5259, hlam, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5261, hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h1, hlam, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h1, h2, h5322, hc02, hc24, hlam, hphi, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5316, hlam, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5215, h5330, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h0, h5259, hc12, hc24, hlam, hphi, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5316, hc03, hc34, hlam, hphi, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h0, h5261, h5316, hc12, hc34, hlam, hphi, ht23, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5214, hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h0, h2, h5214, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5318, hlam, p5335_0]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [h5319, hlam, p5335_1]
                                      · have p5335_0 := h5335c.1
                                        have p5335_1 := h5335c.2.1
                                        have p5335_2 := h5335c.2.2.1
                                        have p5335_3 := h5335c.2.2.2
                                        linarith only [hlam, p5335_0]
                                    · linarith only [h1, h2, h5322, h5328, h5330, h5334, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h1, h2, h5322, h5328, h5329, h5333, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h2, h5328, h5332, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1, h2, h5329, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h1, h2, h5318, h5320, h5326, h5328, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h2, h5318, h5319, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5367 | h5367
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5368 | h5368
                  · linarith only [h0, h5215, h5368, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5370 | h5370
                    · linarith only [h0, h5259, h5370, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5372 | h5372
                      · linarith only [h0, h5261, h5372, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5374 | h5374
                        · linarith only [h1, h2, h5215, h5316, h5370, h5374, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5376 | h5376
                          · linarith only [h1, h2, h5214, h5318, h5372, h5374, h5376, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5378 | h5378
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5379 | h5379
                              · linarith only [h0, h2, h5374, h5379, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5381 | h5381
                                · linarith only [h0, h5215, h5318, h5379, h5381, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5383 | h5383
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5384 | h5384
                                    · rcases h0bigk with h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c | h5385c
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h2, h5215, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h2, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h2, h5215, h5318, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5215, hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5259, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5261, hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h1, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h1, h2, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5316, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5318, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h2, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h1, h2, h5368, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h2, h5214, h5368, h5370, h5376, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5214, hlam, p5385_0]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h0, h2, h5214, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h1, h2, h5214, h5368, h5370, hc12, hc24, hlam, hphi, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [h5367, hlam, p5385_1]
                                      · have p5385_0 := h5385c.1
                                        have p5385_1 := h5385c.2.1
                                        have p5385_2 := h5385c.2.2.1
                                        have p5385_3 := h5385c.2.2.2
                                        linarith only [hlam, p5385_0]
                                    · linarith only [h0, h2, h5370, h5379, h5384, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h5214, h5370, h5378, h5383, hlam]
                            · linarith only [h2, h5214, h5368, h5376, h5378, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h5214, h5367, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5415 | h5415
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5416 | h5416
        · linarith only [h0, h2, h5416, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5418 | h5418
          · linarith only [h0, h5214, h5418, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5420 | h5420
            · linarith only [h1, h2, h5420, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5422 | h5422
              · linarith only [h0, h5214, h5415, h5422, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5424 | h5424
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5425 | h5425
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5426 | h5426
                    · linarith only [h0, h2, h5416, h5426, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5428 | h5428
                      · linarith only [h0, h5214, h5418, h5428, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5430 | h5430
                        · linarith only [h0, h5214, h5420, h5424, h5425, h5430, hlam]
                        · linarith only [h0, h2, h5425, h5430, hc23, hc34, hlam, hphi]
                  · linarith only [h5415, h5416, h5425, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5434 | h5434
                  · linarith only [h0, h2, h5424, h5434, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h5415, h5424, h5434, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5437 | h5437
        · linarith only [h1, h2, h5415, h5437, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5439 | h5439
          · linarith only [h1, h5214, h5415, h5439, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5441 | h5441
            · linarith only [h1, h2, h5441, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5443 | h5443
              · linarith only [h1, h5214, h5443, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5445 | h5445
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5446 | h5446
                  · linarith only [h0, h2, h5415, h5446, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5448 | h5448
                    · linarith only [h0, h5214, h5437, h5445, h5448, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5450 | h5450
                      · linarith only [h1, h2, h5439, h5446, h5448, h5450, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5452 | h5452
                        · linarith only [h1, h2, h5441, h5448, h5452, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5454 | h5454
                          · linarith only [h1, h5214, h5443, h5454, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5456 | h5456
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h5457 | h5457
                              · linarith only [h0, h5214, h5452, h5456, h5457, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h5459 | h5459
                                · linarith only [h1, h5214, h5446, h5454, h5459, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h5461 | h5461
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5462 | h5462
                                    · rcases h0bigk with h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c | h5463c
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h5214, h5456, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h5214, h5415, h5448, h5456, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h2, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5214, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5415, hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5437, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5439, hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h1, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h1, h5214, h5448, h5456, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5441, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5443, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h2, h5448, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h2, h5415, h5448, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [hlam, p5463_0]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h2, h5214, h5448, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h5214, h5448, h5456, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h0, h5214, h5415, h5448, h5456, hc12, hc24, hlam, hphi, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [h5445, hlam, p5463_1]
                                      · have p5463_0 := h5463c.1
                                        have p5463_1 := h5463c.2.1
                                        have p5463_2 := h5463c.2.2.1
                                        have p5463_3 := h5463c.2.2.2
                                        linarith only [hlam, p5463_0]
                                    · linarith only [h2, h5445, h5448, h5457, h5462, hlam]
                                  · linarith only [h2, h5445, h5448, h5461, hlam]
                            · linarith only [h2, h5445, h5456, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5492 | h5492
                  · linarith only [h0, h2, h5445, h5492, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5494 | h5494
                    · linarith only [h1, h2, h5445, h5492, h5494, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5496 | h5496
                      · linarith only [h0, h5439, h5496, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5498 | h5498
                        · linarith only [h1, h2, h5445, h5498, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h5500 | h5500
                          · linarith only [h1, h2, h5415, h5443, h5445, h5500, hc02, hc45, hlam, hphi, ht23, ht34]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h5502 | h5502
                            · linarith only [h0, h2, h5445, h5498, h5502, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h2, h5492, h5502, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
