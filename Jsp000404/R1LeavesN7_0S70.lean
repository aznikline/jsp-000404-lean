import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S69

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7280000 in
set_option maxHeartbeats 7280000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s31 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h33187 := hg33187
  rcases m.htr 0 1 4 (by decide) (by decide) with h33188 | h33188
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s32 m hb1 hb2 hb4 hb5 h0 h33187 h33188
  · rcases m.htr 0 1 5 (by decide) (by decide) with h36282 | h36282
    · rcases m.htr 0 2 3 (by decide) (by decide) with h36283 | h36283
      · rcases m.htr 0 2 4 (by decide) (by decide) with h36284 | h36284
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36285 | h36285
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36286 | h36286
            · linarith only [h33187, h33188, h36286, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36288 | h36288
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36289 | h36289
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36290 | h36290
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36291 | h36291
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36292 | h36292
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36293 | h36293
                        · linarith only [h33187, h33188, h36286, h36291, h36293, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36295 | h36295
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36296 | h36296
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36297 | h36297
                              · linarith only [h33187, h33188, h36290, h36293, h36297, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36299 | h36299
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36300 | h36300
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36301 | h36301
                                    · rcases h1bigk with h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c | h36302c
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h0, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33188, h36290, h36293, h36299, h36301, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p36302_1]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33188, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        rcases p36302_3 (m.d 0 1) (by simp) with h36307 | h36307
                                        · rcases p36302_3 (m.d 1 2) (by simp) with h36308 | h36308
                                          · rcases p36302_3 (m.d 1 3) (by simp) with h36309 | h36309
                                            · linarith only [h33187, h36309, hlam]
                                            · linarith only [h36295, h36309, hlam]
                                          · linarith only [h36292, h36308, hlam]
                                        · linarith only [h36307, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33187, h36290, h36299, h36301, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p36302_1]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        rcases p36302_3 (m.d 0 1) (by simp) with h36316 | h36316
                                        · linarith only [h0, h36316, hlam]
                                        · linarith only [h33187, h36316, hlam]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33187, h33188, h36290, h36299, h36301, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p36302_1]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        rcases p36302_3 (m.d 0 1) (by simp) with h36320 | h36320
                                        · linarith only [h0, h36320, hlam]
                                        · linarith only [h36282, h36320, hlam]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33187, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36290, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36293, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33187, h33188, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p36302_1]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h33187, h36290, h36299, h36301, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p36302_1]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36291, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        rcases p36302_3 (m.d 0 1) (by simp) with h36330 | h36330
                                        · linarith only [h33188, h36330, hlam]
                                        · linarith only [h33187, h36330, hlam]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        rcases p36302_3 (m.d 0 1) (by simp) with h36334 | h36334
                                        · linarith only [h33188, h36334, hlam]
                                        · linarith only [h36282, h36334, hlam]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36282, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36292, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36295, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [h36296, hlam, p36302_0]
                                      · have p36302_0 := h36302c.1
                                        have p36302_1 := h36302c.2.1
                                        have p36302_2 := h36302c.2.2.1
                                        have p36302_3 := h36302c.2.2.2
                                        linarith only [hlam, p36302_0]
                                    · linarith only [h33187, h33188, h36293, h36301, hc13, hc45, hlam, hphi, ht34]
                                  · linarith only [h33187, h33188, h36291, h36295, h36296, h36297, h36299, h36300, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h33187, h33188, h36288, h36293, h36299, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36296, hc13, hc45, hlam, hphi, ht34]
                          · linarith only [h33187, h33188, h36288, h36293, h36295, hc13, hc34, hlam, hphi]
                      · linarith only [h33187, h33188, h36285, h36288, h36291, h36292, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h36284, h36291, hlam]
                  · linarith only [h0, h36283, h36290, hlam]
                · linarith only [h33187, h33188, h36288, h36289, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36351 | h36351
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36352 | h36352
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36353 | h36353
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36354 | h36354
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36355 | h36355
                        · linarith only [h33187, h33188, h36286, h36355, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36357 | h36357
                          · linarith only [h33187, h33188, h36288, h36357, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36359 | h36359
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36360 | h36360
                              · linarith only [h33187, h33188, h36352, h36355, h36360, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36362 | h36362
                                · linarith only [h33187, h36288, h36352, h36362, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36364 | h36364
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36365 | h36365
                                    · rcases h1bigk with h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c | h36366c
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h0, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h33188, h36352, h36355, hc23, hc34, hlam, hphi, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h33188, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h33188, h36354, h36355, h36362, hc23, hc34, hlam, hphi, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        rcases p36366_3 (m.d 0 1) (by simp) with h36372 | h36372
                                        · linarith only [h36372, hlam, p36366_0]
                                        · rcases p36366_3 (m.d 1 2) (by simp) with h36374 | h36374
                                          · rcases p36366_3 (m.d 1 3) (by simp) with h36375 | h36375
                                            · linarith only [h36352, h36375, hlam]
                                            · rcases p36366_3 (m.d 1 4) (by simp) with h36377 | h36377
                                              · linarith only [h36353, h36377, hlam]
                                              · linarith only [h33188, h36377, hlam]
                                          · linarith only [h36374, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        rcases p36366_3 (m.d 0 1) (by simp) with h36382 | h36382
                                        · linarith only [h0, h36382, hlam]
                                        · linarith only [h33187, h36382, hlam]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h33188, hc01, hc12, hlam, hphi, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        rcases p36366_3 (m.d 0 1) (by simp) with h36386 | h36386
                                        · linarith only [h0, h36386, hlam]
                                        · linarith only [h36282, h36386, hlam]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h33187, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36352, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36355, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36357, hlam, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36282, h36352, h36355, h36357, hc23, hc34, hlam, hphi, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36353, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        rcases p36366_3 (m.d 0 1) (by simp) with h36396 | h36396
                                        · linarith only [h33188, h36396, hlam]
                                        · linarith only [h33187, h36396, hlam]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        rcases p36366_3 (m.d 0 1) (by simp) with h36400 | h36400
                                        · linarith only [h33188, h36400, hlam]
                                        · linarith only [h36282, h36400, hlam]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36282, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36354, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h0, h36282, h36352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36366_1]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [h36359, hlam, p36366_0]
                                      · have p36366_0 := h36366c.1
                                        have p36366_1 := h36366c.2.1
                                        have p36366_2 := h36366c.2.2.1
                                        have p36366_3 := h36366c.2.2.2
                                        linarith only [hlam, p36366_0]
                                    · linarith only [h33187, h33188, h36352, h36355, h36365, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h33188, h36282, h36355, h36359, h36360, h36364, hc23, hc34, hlam, hphi]
                            · linarith only [h33188, h36282, h36357, h36359, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h36285, h36354, hlam]
                    · linarith only [h0, h36284, h36353, hlam]
                  · linarith only [h0, h33187, h36283, h36352, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h33188, h36282, h36351, hlam]
          · linarith only [h0, h36282, h36285, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36416 | h36416
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36417 | h36417
            · linarith only [h0, h33187, h36284, h36417, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36419 | h36419
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36420 | h36420
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36421 | h36421
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36422 | h36422
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36423 | h36423
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36424 | h36424
                        · linarith only [h0, h33187, h36284, h36417, h36422, h36424, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36426 | h36426
                          · linarith only [h0, h33187, h36284, h36422, h36426, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h0, h33187, h36284, h36419, h36421, h36422, h36426, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h36284, h36422, h36423, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36430 | h36430
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36431 | h36431
                        · linarith only [h0, h33187, h36417, h36422, h36431, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36433 | h36433
                          · linarith only [h0, h33187, h36422, h36433, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h33187, h36419, h36421, h36422, h36433, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · linarith only [h0, h36282, h36284, h36416, h36430, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h36283, h36421, hlam]
                · linarith only [h0, h33187, h36284, h36419, h36420, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36439 | h36439
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36440 | h36440
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36441 | h36441
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36442 | h36442
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36443 | h36443
                        · linarith only [h0, h33187, h36284, h36417, h36441, h36443, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36445 | h36445
                          · linarith only [h0, h33187, h36284, h36419, h36441, h36445, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36447 | h36447
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36448 | h36448
                              · linarith only [h33188, h36282, h36283, h36443, h36445, h36448, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36450 | h36450
                                · linarith only [h0, h36282, h36284, h36419, h36440, h36441, h36445, h36450, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36452 | h36452
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36453 | h36453
                                    · rcases h1bigk with h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c | h36454c
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h36284, h36441, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h33188, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h36284, h36441, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        rcases p36454_3 (m.d 0 1) (by simp) with h36460 | h36460
                                        · linarith only [h36460, hlam, p36454_0]
                                        · rcases p36454_3 (m.d 1 2) (by simp) with h36462 | h36462
                                          · rcases p36454_3 (m.d 1 3) (by simp) with h36463 | h36463
                                            · linarith only [h36440, h36463, hlam]
                                            · rcases p36454_3 (m.d 1 4) (by simp) with h36465 | h36465
                                              · linarith only [h36441, h36465, hlam]
                                              · linarith only [h33188, h36465, hlam]
                                          · linarith only [h36462, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h33187, h36284, h36441, hlam, p36454_2]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h36284, h36441, hc01, hc12, hlam, hphi, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h36282, h36284, h36441, hlam, p36454_2]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h33187, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36440, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36443, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36445, hlam, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36282, h36442, h36443, h36450, hc23, hc34, hlam, hphi, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36441, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        rcases p36454_3 (m.d 0 1) (by simp) with h36480 | h36480
                                        · linarith only [h33188, h36480, hlam]
                                        · linarith only [h33187, h36480, hlam]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        rcases p36454_3 (m.d 0 1) (by simp) with h36484 | h36484
                                        · linarith only [h33188, h36484, hlam]
                                        · linarith only [h36282, h36484, hlam]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36282, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36442, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h0, h36282, h36284, h36440, h36441, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36454_1]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [h36447, hlam, p36454_0]
                                      · have p36454_0 := h36454c.1
                                        have p36454_1 := h36454c.2.1
                                        have p36454_2 := h36454c.2.2.1
                                        have p36454_3 := h36454c.2.2.2
                                        linarith only [hlam, p36454_0]
                                    · linarith only [h33187, h33188, h36440, h36443, h36453, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h36282, h36284, h36447, h36452, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h36282, h36284, h36439, h36441, h36447, hlam]
                      · linarith only [h36284, h36416, h36442, hc12, hc24, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36496 | h36496
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36497 | h36497
                        · linarith only [h0, h33187, h36417, h36441, h36497, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36499 | h36499
                          · linarith only [h0, h33187, h36441, h36499, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36501 | h36501
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36502 | h36502
                              · linarith only [h0, h36282, h36440, h36441, h36497, h36499, h36502, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h36282, h36441, h36499, h36502, hc13, hc34, hlam, hphi]
                            · linarith only [h0, h36282, h36440, h36441, h36499, h36501, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h36282, h36284, h36416, h36496, hc04, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h36283, h36440, hlam]
                · linarith only [h0, h36282, h36284, h36439, hlam]
          · linarith only [h0, h36282, h36416, hlam]
      · linarith only [h0, h33187, h36283, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h36511 | h36511
      · rcases m.htr 0 2 4 (by decide) (by decide) with h36512 | h36512
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36513 | h36513
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36514 | h36514
            · linarith only [h33187, h33188, h36514, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36516 | h36516
              · linarith only [h33187, h36282, h36516, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36518 | h36518
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36519 | h36519
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36520 | h36520
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36521 | h36521
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36522 | h36522
                        · linarith only [h33187, h33188, h36514, h36520, h36522, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36524 | h36524
                          · linarith only [h33187, h36282, h36516, h36524, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36526 | h36526
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36527 | h36527
                              · linarith only [h33187, h36282, h36511, h36522, h36526, h36527, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36529 | h36529
                                · linarith only [h33187, h36282, h36519, h36524, h36529, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36531 | h36531
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36532 | h36532
                                    · rcases h1bigk with h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c | h36533c
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h0, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36282, h36519, h36522, h36526, hc23, hc34, hlam, hphi, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33188, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36282, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        rcases p36533_3 (m.d 0 1) (by simp) with h36539 | h36539
                                        · linarith only [h36539, hlam, p36533_0]
                                        · rcases p36533_3 (m.d 1 2) (by simp) with h36541 | h36541
                                          · rcases p36533_3 (m.d 1 3) (by simp) with h36542 | h36542
                                            · linarith only [h36519, h36542, hlam]
                                            · rcases p36533_3 (m.d 1 4) (by simp) with h36544 | h36544
                                              · linarith only [h36520, h36544, hlam]
                                              · linarith only [h33188, h36544, hlam]
                                          · linarith only [h36541, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        rcases p36533_3 (m.d 0 1) (by simp) with h36549 | h36549
                                        · linarith only [h0, h36549, hlam]
                                        · linarith only [h33187, h36549, hlam]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33188, hc01, hc12, hlam, hphi, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33187, h36282, h36519, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33187, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36519, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36522, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36524, hlam, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33187, h36519, h36522, hc23, hc34, hlam, hphi, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36520, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        rcases p36533_3 (m.d 0 1) (by simp) with h36561 | h36561
                                        · linarith only [h33188, h36561, hlam]
                                        · linarith only [h33187, h36561, hlam]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33187, h36282, h36519, h36522, hc23, hc34, hlam, hphi, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h33187, h36519, h36524, hc23, hc35, hlam, hphi, p36533_1]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36521, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        rcases p36533_3 (m.d 0 1) (by simp) with h36568 | h36568
                                        · linarith only [h36282, h36568, hlam]
                                        · linarith only [h33187, h36568, hlam]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [h36526, hlam, p36533_0]
                                      · have p36533_0 := h36533c.1
                                        have p36533_1 := h36533c.2.1
                                        have p36533_2 := h36533c.2.2.1
                                        have p36533_3 := h36533c.2.2.2
                                        linarith only [hlam, p36533_0]
                                    · linarith only [h33187, h33188, h36519, h36522, h36531, h36532, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36574 | h36574
                                    · rcases h1bigk with h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c | h36575c
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h0, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36282, h36519, h36522, h36526, hc23, hc34, hlam, hphi, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33188, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36282, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        rcases p36575_3 (m.d 0 1) (by simp) with h36581 | h36581
                                        · linarith only [h36581, hlam, p36575_0]
                                        · rcases p36575_3 (m.d 1 2) (by simp) with h36583 | h36583
                                          · rcases p36575_3 (m.d 1 3) (by simp) with h36584 | h36584
                                            · linarith only [h36519, h36584, hlam]
                                            · rcases p36575_3 (m.d 1 4) (by simp) with h36586 | h36586
                                              · linarith only [h36520, h36586, hlam]
                                              · linarith only [h33188, h36586, hlam]
                                          · linarith only [h36583, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        rcases p36575_3 (m.d 0 1) (by simp) with h36591 | h36591
                                        · linarith only [h0, h36591, hlam]
                                        · linarith only [h33187, h36591, hlam]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33188, h36518, h36531, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36282, hc01, hc12, hlam, hphi, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33187, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36519, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36522, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36524, hlam, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33187, h36519, h36522, hc23, hc34, hlam, hphi, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36520, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        rcases p36575_3 (m.d 0 1) (by simp) with h36603 | h36603
                                        · linarith only [h33188, h36603, hlam]
                                        · linarith only [h33187, h36603, hlam]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33187, h36282, h36519, h36522, hc23, hc34, hlam, hphi, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h33187, h36519, h36524, hc23, hc35, hlam, hphi, p36575_1]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36521, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        rcases p36575_3 (m.d 0 1) (by simp) with h36610 | h36610
                                        · linarith only [h36282, h36610, hlam]
                                        · linarith only [h33187, h36610, hlam]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [h36526, hlam, p36575_0]
                                      · have p36575_0 := h36575c.1
                                        have p36575_1 := h36575c.2.1
                                        have p36575_2 := h36575c.2.2.1
                                        have p36575_3 := h36575c.2.2.2
                                        linarith only [hlam, p36575_0]
                                    · linarith only [h33187, h33188, h36518, h36519, h36522, h36574, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h33187, h33188, h36519, h36526, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h36512, h36513, h36518, h36521, hlam]
                    · linarith only [h0, h36512, h36520, hlam]
                  · linarith only [h0, h36511, h36519, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36620 | h36620
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36621 | h36621
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36622 | h36622
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36623 | h36623
                        · linarith only [h33187, h33188, h36518, h36623, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36625 | h36625
                          · linarith only [h33187, h36516, h36625, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36627 | h36627
                            · linarith only [h33187, h33188, h36518, h36620, h36623, h36627, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36620, h36627, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h33187, h36513, h36620, h36622, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h36512, h36621, hlam]
                  · linarith only [h0, h36511, h36620, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36633 | h36633
            · linarith only [h33187, h33188, h36633, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36635 | h36635
              · linarith only [h33187, h33188, h36512, h36513, h36635, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36637 | h36637
                · linarith only [h36512, h36513, h36637, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36639 | h36639
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36640 | h36640
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36641 | h36641
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36642 | h36642
                        · linarith only [h33187, h33188, h36512, h36513, h36633, h36641, h36642, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36644 | h36644
                          · linarith only [h33187, h33188, h36512, h36513, h36635, h36644, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36646 | h36646
                            · linarith only [h33187, h33188, h36637, h36642, h36646, hc13, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36639, h36646, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36649 | h36649
                        · linarith only [h33187, h33188, h36640, h36641, h36649, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36651 | h36651
                          · linarith only [h33187, h33188, h36640, h36641, h36651, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36653 | h36653
                            · linarith only [h33187, h33188, h36637, h36639, h36640, h36641, h36653, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h33187, h33188, h36639, h36653, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h33187, h36512, h36639, h36640, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h36511, h36639, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h36658 | h36658
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36659 | h36659
            · linarith only [h0, h33187, h36512, h36659, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36661 | h36661
              · linarith only [h33187, h36282, h36661, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36663 | h36663
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36664 | h36664
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36665 | h36665
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36666 | h36666
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36667 | h36667
                        · linarith only [h33187, h36282, h36512, h36658, h36659, h36665, h36667, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36669 | h36669
                          · linarith only [h33187, h36282, h36661, h36669, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36671 | h36671
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36672 | h36672
                              · linarith only [h36511, h36512, h36665, h36667, h36672, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36674 | h36674
                                · linarith only [h33187, h36282, h36664, h36669, h36674, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36676 | h36676
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36677 | h36677
                                    · rcases h1bigk with h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c | h36678c
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h0, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36282, h36664, h36669, hc23, hc35, hlam, hphi, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33188, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36282, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        rcases p36678_3 (m.d 0 1) (by simp) with h36684 | h36684
                                        · linarith only [h36684, hlam, p36678_0]
                                        · rcases p36678_3 (m.d 1 2) (by simp) with h36686 | h36686
                                          · rcases p36678_3 (m.d 1 3) (by simp) with h36687 | h36687
                                            · linarith only [h36664, h36687, hlam]
                                            · rcases p36678_3 (m.d 1 4) (by simp) with h36689 | h36689
                                              · linarith only [h36665, h36689, hlam]
                                              · linarith only [h33188, h36689, hlam]
                                          · linarith only [h36686, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, h36282, h36512, h36658, h36665, hlam, p36678_2]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36282, h36512, h36658, h36665, hc01, hc12, hlam, hphi, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, h36282, h36664, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36664, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36667, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36669, hlam, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, h36664, h36667, hc23, hc34, hlam, hphi, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36665, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        rcases p36678_3 (m.d 0 1) (by simp) with h36704 | h36704
                                        · linarith only [h33188, h36704, hlam]
                                        · linarith only [h33187, h36704, hlam]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, h36282, h36664, h36667, hc23, hc34, hlam, hphi, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h33187, h36664, h36669, h36677, hc23, hc34, hlam, hphi, p36678_1]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36666, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        rcases p36678_3 (m.d 0 1) (by simp) with h36711 | h36711
                                        · linarith only [h36282, h36711, hlam]
                                        · linarith only [h33187, h36711, hlam]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [h36671, hlam, p36678_0]
                                      · have p36678_0 := h36678c.1
                                        have p36678_1 := h36678c.2.1
                                        have p36678_2 := h36678c.2.2.1
                                        have p36678_3 := h36678c.2.2.2
                                        linarith only [hlam, p36678_0]
                                    · linarith only [h33187, h33188, h36658, h36667, h36676, h36677, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h0, h33187, h36512, h36664, h36676, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h36512, h36658, h36663, h36665, h36671, hlam]
                      · linarith only [h36512, h36658, h36665, h36666, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36720 | h36720
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36721 | h36721
                        · linarith only [h33187, h36282, h36659, h36665, h36720, h36721, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36723 | h36723
                          · linarith only [h33187, h36282, h36665, h36720, h36723, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36725 | h36725
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36726 | h36726
                              · linarith only [h33187, h36282, h36664, h36665, h36720, h36721, h36726, hlam]
                              · linarith only [h33187, h36282, h36664, h36665, h36720, h36726, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h36282, h36663, h36664, h36665, h36720, h36725, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h33187, h36658, h36664, h36720, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h36511, h36664, hlam]
                · linarith only [h36512, h36658, h36663, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h36733 | h36733
            · linarith only [h0, h33187, h36512, h36733, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h36735 | h36735
              · linarith only [h33187, h36282, h36735, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36737 | h36737
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36738 | h36738
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36739 | h36739
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36740 | h36740
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36741 | h36741
                        · linarith only [h0, h33187, h36512, h36733, h36739, h36741, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36743 | h36743
                          · linarith only [h0, h33187, h36658, h36735, h36743, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36745 | h36745
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36746 | h36746
                              · linarith only [h33188, h36511, h36512, h36739, h36741, h36746, hc01, hc12, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h36748 | h36748
                                · linarith only [h0, h33187, h36658, h36738, h36740, h36743, h36748, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h36750 | h36750
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h36751 | h36751
                                    · rcases h1bigk with h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c | h36752c
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h0, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h0, h36658, h36738, h36740, h36741, h36745, hc23, hc34, hlam, hphi, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33188, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36282, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        rcases p36752_3 (m.d 0 1) (by simp) with h36758 | h36758
                                        · linarith only [h36758, hlam, p36752_0]
                                        · rcases p36752_3 (m.d 1 2) (by simp) with h36760 | h36760
                                          · rcases p36752_3 (m.d 1 3) (by simp) with h36761 | h36761
                                            · linarith only [h36738, h36761, hlam]
                                            · rcases p36752_3 (m.d 1 4) (by simp) with h36763 | h36763
                                              · linarith only [h36739, h36763, hlam]
                                              · linarith only [h33188, h36763, hlam]
                                          · linarith only [h36760, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h0, h33187, h36658, h36739, h36750, hlam, p36752_2]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33188, hc01, hc12, hlam, hphi, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33187, h36282, h36738, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33187, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36738, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36741, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36743, hlam, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33187, h36738, h36741, hc23, hc34, hlam, hphi, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36739, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        rcases p36752_3 (m.d 0 1) (by simp) with h36778 | h36778
                                        · linarith only [h33188, h36778, hlam]
                                        · linarith only [h33187, h36778, hlam]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36658, h36740, h36741, hc02, hc34, hlam, hphi, ht23, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h33187, h36738, h36743, hc23, hc35, hlam, hphi, p36752_1]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36740, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        rcases p36752_3 (m.d 0 1) (by simp) with h36785 | h36785
                                        · linarith only [h36282, h36785, hlam]
                                        · linarith only [h33187, h36785, hlam]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [h36745, hlam, p36752_0]
                                      · have p36752_0 := h36752c.1
                                        have p36752_1 := h36752c.2.1
                                        have p36752_2 := h36752c.2.2.1
                                        have p36752_3 := h36752c.2.2.2
                                        linarith only [hlam, p36752_0]
                                    · linarith only [h33187, h33188, h36738, h36741, h36751, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h33187, h33188, h36512, h36737, h36738, h36741, h36750, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36738, h36745, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h33187, h36512, h36738, h36739, h36740, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36794 | h36794
                      · linarith only [h0, h33187, h36658, h36738, h36739, h36794, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36796 | h36796
                        · linarith only [h0, h33187, h36739, h36796, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36798 | h36798
                          · linarith only [h0, h33187, h36739, h36798, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36800 | h36800
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h36801 | h36801
                              · linarith only [h0, h33187, h36738, h36739, h36796, h36801, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h33187, h36738, h36739, h36801, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36738, h36800, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h33187, h36511, h36658, h36737, h36738, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h36806 | h36806
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h36807 | h36807
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36808 | h36808
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36809 | h36809
                        · linarith only [h0, h33187, h36512, h36807, h36809, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36811 | h36811
                          · linarith only [h0, h33187, h36512, h36807, h36811, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36813 | h36813
                            · linarith only [h0, h33187, h36512, h36737, h36806, h36809, h36813, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36806, h36813, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h36512, h36807, h36808, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h36817 | h36817
                      · linarith only [h0, h33187, h36658, h36806, h36807, h36817, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h36819 | h36819
                        · linarith only [h0, h33187, h36807, h36819, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36821 | h36821
                          · linarith only [h0, h33187, h36807, h36821, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h36823 | h36823
                            · linarith only [h33187, h33188, h36737, h36806, h36819, h36823, hc23, hc34, hlam, hphi]
                            · linarith only [h33187, h33188, h36806, h36823, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h33187, h36511, h36512, h36737, h36806, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h33187, h36511, hlam]

end R2N4
