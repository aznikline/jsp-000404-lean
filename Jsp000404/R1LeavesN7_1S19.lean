import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S17
import Jsp000404.R1LeavesN7_1S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8178000 in
set_option maxHeartbeats 8178000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9965 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12966 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h7821 := hg7821
  have h9029 := hg9029
  rcases m.htr 0 4 5 (by decide) (by decide) with h13290 | h13290
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13291 | h13291
    · linarith only [h0, h13291, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13293 | h13293
      · linarith only [h0, h13293, h7821, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13295 | h13295
        · linarith only [h0, h13295, h9029, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13297 | h13297
          · linarith only [h1, h13297, h9965, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13299 | h13299
            · linarith only [h1, h12966, h13299, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13301 | h13301
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13302 | h13302
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13303 | h13303
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13304 | h13304
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13305 | h13305
                      · rcases h0bigk with h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c | h13306c
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          rcases p13306_3 (m.d 0 1) (by simp) with h13308 | h13308
                          · rcases p13306_3 (m.d 0 2) (by simp) with h13309 | h13309
                            · linarith only [h0, h13309, hlam]
                            · rcases p13306_3 (m.d 0 3) (by simp) with h13311 | h13311
                              · linarith only [h1, h13311, hlam]
                              · linarith only [h13311, h4, hlam]
                          · linarith only [h0, h13308, hlam]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          rcases p13306_3 (m.d 0 1) (by simp) with h13315 | h13315
                          · rcases p13306_3 (m.d 0 2) (by simp) with h13316 | h13316
                            · linarith only [h0, h13316, hlam]
                            · rcases p13306_3 (m.d 0 3) (by simp) with h13318 | h13318
                              · linarith only [h1, h13318, hlam]
                              · rcases p13306_3 (m.d 0 4) (by simp) with h13320 | h13320
                                · linarith only [h13320, h2, hlam]
                                · linarith only [h13320, h9965, hlam]
                          · linarith only [h1, h13315, hlam]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          rcases p13306_3 (m.d 0 1) (by simp) with h13324 | h13324
                          · rcases p13306_3 (m.d 0 2) (by simp) with h13325 | h13325
                            · linarith only [h0, h13325, hlam]
                            · rcases p13306_3 (m.d 0 3) (by simp) with h13327 | h13327
                              · linarith only [h1, h13327, hlam]
                              · rcases p13306_3 (m.d 0 4) (by simp) with h13329 | h13329
                                · linarith only [h13329, h2, hlam]
                                · rcases p13306_3 (m.d 0 5) (by simp) with h13331 | h13331
                                  · linarith only [h13331, h3, hlam]
                                  · rcases h2bigk with h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c | h13333c
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h4, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h7821, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h9029, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h0, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13291, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13293, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13295, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13344 | h13344
                                      · linarith only [h13344, hlam, p13333_0]
                                      · rcases p13333_3 (m.d 1 2) (by simp) with h13346 | h13346
                                        · linarith only [h13291, h13346, hlam]
                                        · rcases p13333_3 (m.d 2 3) (by simp) with h13348 | h13348
                                          · rcases p13333_3 (m.d 2 4) (by simp) with h13349 | h13349
                                            · linarith only [h13302, h13349, hlam]
                                            · linarith only [h13349, h7821, hlam]
                                          · linarith only [h13348, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13353 | h13353
                                      · linarith only [h13353, h4, hlam]
                                      · linarith only [h0, h13353, hlam]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h12966, h13303, h13304, h4, hc02, hc23, hlam, hphi, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h0, h12966, h13303, h4, hc12, hc23, hlam, hphi, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13359 | h13359
                                      · linarith only [h13359, hlam, p13333_0]
                                      · rcases p13333_3 (m.d 1 2) (by simp) with h13361 | h13361
                                        · linarith only [h13293, h13361, hlam]
                                        · rcases p13333_3 (m.d 2 3) (by simp) with h13363 | h13363
                                          · rcases p13333_3 (m.d 2 4) (by simp) with h13364 | h13364
                                            · rcases p13333_3 (m.d 2 5) (by simp) with h13365 | h13365
                                              · linarith only [h13304, h13365, hlam]
                                              · linarith only [h13365, h9029, hlam]
                                            · linarith only [h13364, hlam, p13333_0]
                                          · linarith only [h13363, h4, hlam]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13370 | h13370
                                      · linarith only [h13370, h7821, hlam]
                                      · linarith only [h0, h13370, hlam]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13302, hlam, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h0, h12966, h13303, h4, hc12, hc24, hlam, hphi, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13376 | h13376
                                      · linarith only [h13376, hlam, p13333_0]
                                      · rcases p13333_3 (m.d 1 2) (by simp) with h13378 | h13378
                                        · linarith only [h13295, h13378, hlam]
                                        · rcases p13333_3 (m.d 2 3) (by simp) with h13380 | h13380
                                          · rcases p13333_3 (m.d 2 4) (by simp) with h13381 | h13381
                                            · rcases p13333_3 (m.d 2 5) (by simp) with h13382 | h13382
                                              · rcases h3bigk with h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c | h13383c
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h12966, h13290, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p13306_1, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h4, hlam, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h9965, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h12966, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13291, hlam, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13297, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13299, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  rcases p13383_3 (m.d 0 3) (by simp) with h13394 | h13394
                                                  · linarith only [h13394, h4, hlam]
                                                  · rcases p13383_3 (m.d 1 3) (by simp) with h13396 | h13396
                                                    · linarith only [h13291, h13396, hlam]
                                                    · rcases p13383_3 (m.d 2 3) (by simp) with h13398 | h13398
                                                      · rcases p13383_3 (m.d 3 4) (by simp) with h13399 | h13399
                                                        · linarith only [h13302, h13399, hlam]
                                                        · linarith only [h13399, h9965, hlam]
                                                      · linarith only [h13398, h4, hlam]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  rcases p13383_3 (m.d 0 3) (by simp) with h13403 | h13403
                                                  · linarith only [h13403, h4, hlam]
                                                  · linarith only [h1, h13403, hlam]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, h12966, h13291, h13305, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, h12966, h13291, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, h13291, h13302, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13291, h13302, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13302, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, h12966, h13291, h13302, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h1, h13291, h13303, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13291, h13303, hc12, hc23, hlam, hphi, p13383_1]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13303, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [h13305, hlam, p13383_0]
                                                · have p13383_0 := h13383c.1
                                                  have p13383_1 := h13383c.2.1
                                                  have p13383_2 := h13383c.2.2.1
                                                  have p13383_3 := h13383c.2.2.2
                                                  linarith only [hlam, p13383_0]
                                              · linarith only [h13382, hlam, p13333_0]
                                            · linarith only [h13381, h7821, hlam]
                                          · linarith only [h13380, h4, hlam]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      rcases p13333_3 (m.d 0 2) (by simp) with h13422 | h13422
                                      · linarith only [h13422, h9029, hlam]
                                      · linarith only [h0, h13422, hlam]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13303, hlam, p13333_1]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [h13304, hlam, p13333_0]
                                    · have p13333_0 := h13333c.1
                                      have p13333_1 := h13333c.2.1
                                      have p13333_2 := h13333c.2.2.1
                                      have p13333_3 := h13333c.2.2.2
                                      linarith only [hlam, p13333_0]
                          · linarith only [h13324, h2, hlam]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          rcases p13306_3 (m.d 0 1) (by simp) with h13429 | h13429
                          · rcases p13306_3 (m.d 0 2) (by simp) with h13430 | h13430
                            · linarith only [h0, h13430, hlam]
                            · rcases p13306_3 (m.d 0 3) (by simp) with h13432 | h13432
                              · linarith only [h1, h13432, hlam]
                              · rcases p13306_3 (m.d 0 4) (by simp) with h13434 | h13434
                                · linarith only [h13434, h2, hlam]
                                · linarith only [h13290, h13434, hlam]
                          · linarith only [h13429, h3, hlam]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h0, hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h4, hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h7821, hlam, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h9029, hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h1, hlam, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h0, h13302, h9965, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h9965, hlam, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h12966, hlam, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h2, hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h0, h13302, h9965, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h1, h13291, h13302, h9965, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h13291, h13299, h13302, h3, h9965, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h3, hlam, p13306_0]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h0, h12966, h13302, h13305, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h1, h12966, h13291, h13302, h13305, hc12, hc23, hlam, hphi, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [h13290, hlam, p13306_1]
                        · have p13306_0 := h13306c.1
                          have p13306_1 := h13306c.2.1
                          have p13306_2 := h13306c.2.2.1
                          have p13306_3 := h13306c.2.2.2
                          linarith only [hlam, p13306_0]
                      · linarith only [h13301, h13305, h2, h9965, hlam]
                    · linarith only [h13290, h13301, h13304, h3, h7821, hlam]
                  · linarith only [h13302, h13303, h9965, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13461 | h13461
                  · linarith only [h12966, h13302, h13461, h4, hc02, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13463 | h13463
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13464 | h13464
                      · rcases h0bigk with h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c | h13465c
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13467 | h13467
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13468 | h13468
                            · linarith only [h0, h13468, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13470 | h13470
                              · linarith only [h1, h13470, hlam]
                              · linarith only [h13470, h4, hlam]
                          · linarith only [h0, h13467, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13474 | h13474
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13475 | h13475
                            · linarith only [h0, h13475, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13477 | h13477
                              · linarith only [h1, h13477, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13479 | h13479
                                · linarith only [h13479, h2, hlam]
                                · linarith only [h13479, h9965, hlam]
                          · linarith only [h1, h13474, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13483 | h13483
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13484 | h13484
                            · linarith only [h0, h13484, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13486 | h13486
                              · linarith only [h1, h13486, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13488 | h13488
                                · linarith only [h13488, h2, hlam]
                                · rcases p13465_3 (m.d 0 5) (by simp) with h13490 | h13490
                                  · linarith only [h13490, h3, hlam]
                                  · rcases h2bigk with h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c | h13492c
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13461, h13464, h4, hc12, hc34, hlam, hphi, ht23, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h4, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h7821, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h9029, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h0, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13291, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13293, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13295, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13461, h13464, hc02, hc34, hlam, hphi, ht23, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13461, h13464, hc12, hc34, hlam, hphi, ht23, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13302, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13461, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      rcases p13492_3 (m.d 0 2) (by simp) with h13508 | h13508
                                      · linarith only [h13508, hlam, p13492_0]
                                      · rcases p13492_3 (m.d 1 2) (by simp) with h13510 | h13510
                                        · linarith only [h13293, h13510, hlam]
                                        · rcases p13492_3 (m.d 2 3) (by simp) with h13512 | h13512
                                          · linarith only [h13302, h13512, hlam]
                                          · linarith only [h13512, h4, hlam]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      rcases p13492_3 (m.d 0 2) (by simp) with h13515 | h13515
                                      · linarith only [h13515, h7821, hlam]
                                      · linarith only [h0, h13515, hlam]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h0, h13302, h13461, h4, hc12, hc34, hlam, hphi, ht23, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      rcases p13492_3 (m.d 0 2) (by simp) with h13521 | h13521
                                      · linarith only [h13521, hlam, p13492_0]
                                      · rcases p13492_3 (m.d 1 2) (by simp) with h13523 | h13523
                                        · linarith only [h13295, h13523, hlam]
                                        · rcases p13492_3 (m.d 2 3) (by simp) with h13525 | h13525
                                          · linarith only [h13461, h13525, hlam]
                                          · linarith only [h13525, h4, hlam]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      rcases p13492_3 (m.d 0 2) (by simp) with h13528 | h13528
                                      · linarith only [h13528, h9029, hlam]
                                      · linarith only [h0, h13528, hlam]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p13492_1]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [h13463, hlam, p13492_0]
                                    · have p13492_0 := h13492c.1
                                      have p13492_1 := h13492c.2.1
                                      have p13492_2 := h13492c.2.2.1
                                      have p13492_3 := h13492c.2.2.2
                                      linarith only [hlam, p13492_0]
                          · linarith only [h13483, h2, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13535 | h13535
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13536 | h13536
                            · linarith only [h0, h13536, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13538 | h13538
                              · linarith only [h1, h13538, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13540 | h13540
                                · linarith only [h13540, h2, hlam]
                                · linarith only [h13290, h13540, hlam]
                          · linarith only [h13535, h3, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h0, hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h4, hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h7821, hlam, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h9029, hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h1, hlam, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h0, h9965, hc12, hc34, hlam, hphi, ht23, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h9965, hlam, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h12966, hlam, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h2, hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13555 | h13555
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13556 | h13556
                            · linarith only [h13556, h7821, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13558 | h13558
                              · linarith only [h13558, h9965, hlam]
                              · linarith only [h13558, h4, hlam]
                          · linarith only [h0, h13555, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13562 | h13562
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13563 | h13563
                            · linarith only [h13563, h7821, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13565 | h13565
                              · linarith only [h13565, h9965, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13567 | h13567
                                · rcases p13465_3 (m.d 0 5) (by simp) with h13568 | h13568
                                  · linarith only [h13290, h13568, hlam]
                                  · linarith only [h12966, h13568, hlam]
                                · linarith only [h13567, h9965, hlam]
                          · linarith only [h1, h13562, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13574 | h13574
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13575 | h13575
                            · linarith only [h13575, h7821, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13577 | h13577
                              · linarith only [h13577, h9965, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13579 | h13579
                                · rcases p13465_3 (m.d 0 5) (by simp) with h13580 | h13580
                                  · linarith only [h13290, h13580, hlam]
                                  · rcases h2bigk with h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13461, h13464, h4, hc12, hc34, hlam, hphi, ht23, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h4, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h7821, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h9029, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h0, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13291, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13293, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13295, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13461, h13464, hc02, hc34, hlam, hphi, ht23, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13461, h13464, hc12, hc34, hlam, hphi, ht23, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13302, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13461, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      rcases p13582_3 (m.d 0 2) (by simp) with h13598 | h13598
                                      · linarith only [h13598, hlam, p13582_0]
                                      · rcases p13582_3 (m.d 1 2) (by simp) with h13600 | h13600
                                        · linarith only [h13293, h13600, hlam]
                                        · rcases p13582_3 (m.d 2 3) (by simp) with h13602 | h13602
                                          · linarith only [h13302, h13602, hlam]
                                          · linarith only [h13602, h4, hlam]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      rcases p13582_3 (m.d 0 2) (by simp) with h13605 | h13605
                                      · linarith only [h13605, h7821, hlam]
                                      · linarith only [h0, h13605, hlam]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h0, h13302, h4, hc12, hc34, hlam, hphi, ht23, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h0, h13302, h9029, hc12, hc34, hlam, hphi, ht23, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      rcases p13582_3 (m.d 0 2) (by simp) with h13611 | h13611
                                      · linarith only [h13611, hlam, p13582_0]
                                      · rcases p13582_3 (m.d 1 2) (by simp) with h13613 | h13613
                                        · linarith only [h13295, h13613, hlam]
                                        · rcases p13582_3 (m.d 2 3) (by simp) with h13615 | h13615
                                          · linarith only [h13461, h13615, hlam]
                                          · linarith only [h13615, h4, hlam]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      rcases p13582_3 (m.d 0 2) (by simp) with h13618 | h13618
                                      · linarith only [h13618, h9029, hlam]
                                      · linarith only [h0, h13618, hlam]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p13582_1]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [h13463, hlam, p13582_0]
                                    · have p13582_0 := h13582c.1
                                      have p13582_1 := h13582c.2.1
                                      have p13582_2 := h13582c.2.2.1
                                      have p13582_3 := h13582c.2.2.2
                                      linarith only [hlam, p13582_0]
                                · linarith only [h13290, h13579, hlam]
                          · linarith only [h13574, h3, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h3, hlam, p13465_0]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13627 | h13627
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13628 | h13628
                            · linarith only [h13628, h9029, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13630 | h13630
                              · linarith only [h12966, h13630, hlam]
                              · linarith only [h13630, h4, hlam]
                          · linarith only [h0, h13627, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          rcases p13465_3 (m.d 0 1) (by simp) with h13634 | h13634
                          · rcases p13465_3 (m.d 0 2) (by simp) with h13635 | h13635
                            · linarith only [h13635, h9029, hlam]
                            · rcases p13465_3 (m.d 0 3) (by simp) with h13637 | h13637
                              · linarith only [h12966, h13637, hlam]
                              · rcases p13465_3 (m.d 0 4) (by simp) with h13639 | h13639
                                · rcases p13465_3 (m.d 0 5) (by simp) with h13640 | h13640
                                  · rcases h2bigk with h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c | h13641c
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h4, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h7821, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h9029, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h0, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13291, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13293, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13295, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13302, hc02, hc34, hlam, hphi, ht23, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13302, hc12, hc34, hlam, hphi, ht23, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13302, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13461, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      rcases p13641_3 (m.d 0 2) (by simp) with h13657 | h13657
                                      · linarith only [h13657, hlam, p13641_0]
                                      · rcases p13641_3 (m.d 1 2) (by simp) with h13659 | h13659
                                        · linarith only [h13293, h13659, hlam]
                                        · rcases p13641_3 (m.d 2 3) (by simp) with h13661 | h13661
                                          · linarith only [h13302, h13661, hlam]
                                          · linarith only [h13661, h4, hlam]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      rcases p13641_3 (m.d 0 2) (by simp) with h13664 | h13664
                                      · linarith only [h13664, h7821, hlam]
                                      · linarith only [h0, h13664, hlam]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h0, h13302, h4, hc12, hc34, hlam, hphi, ht23, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h0, h13302, h9029, hc12, hc34, hlam, hphi, ht23, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      rcases p13641_3 (m.d 0 2) (by simp) with h13670 | h13670
                                      · linarith only [h13670, hlam, p13641_0]
                                      · rcases p13641_3 (m.d 1 2) (by simp) with h13672 | h13672
                                        · linarith only [h13295, h13672, hlam]
                                        · rcases p13641_3 (m.d 2 3) (by simp) with h13674 | h13674
                                          · linarith only [h13461, h13674, hlam]
                                          · linarith only [h13674, h4, hlam]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      rcases p13641_3 (m.d 0 2) (by simp) with h13677 | h13677
                                      · linarith only [h13677, h9029, hlam]
                                      · linarith only [h0, h13677, hlam]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p13641_1]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [h13463, hlam, p13641_0]
                                    · have p13641_0 := h13641c.1
                                      have p13641_1 := h13641c.2.1
                                      have p13641_2 := h13641c.2.2.1
                                      have p13641_3 := h13641c.2.2.2
                                      linarith only [hlam, p13641_0]
                                  · linarith only [h12966, h13640, hlam]
                                · linarith only [h13639, h9965, hlam]
                          · linarith only [h1, h13634, hlam]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [h13290, hlam, p13465_1]
                        · have p13465_0 := h13465c.1
                          have p13465_1 := h13465c.2.1
                          have p13465_2 := h13465c.2.2.1
                          have p13465_3 := h13465c.2.2.2
                          linarith only [hlam, p13465_0]
                      · linarith only [h13290, h13302, h13464, h7821, hlam]
                    · linarith only [h13301, h13463, h2, h7821, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13690 | h13690
                · linarith only [h13290, h13291, h13297, h13301, h13690, h9965, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13692 | h13692
                  · linarith only [h1, h12966, h13291, h13690, h13692, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13694 | h13694
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13695 | h13695
                      · rcases h0bigk with h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c | h13696c
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13698 | h13698
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13699 | h13699
                            · linarith only [h0, h13699, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13701 | h13701
                              · linarith only [h1, h13701, hlam]
                              · linarith only [h13701, h4, hlam]
                          · linarith only [h0, h13698, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13705 | h13705
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13706 | h13706
                            · linarith only [h0, h13706, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13708 | h13708
                              · linarith only [h1, h13708, hlam]
                              · rcases p13696_3 (m.d 0 4) (by simp) with h13710 | h13710
                                · linarith only [h13710, h2, hlam]
                                · linarith only [h13710, h9965, hlam]
                          · linarith only [h1, h13705, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h13290, h13291, h13297, h13301, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13715 | h13715
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13716 | h13716
                            · linarith only [h0, h13716, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13718 | h13718
                              · linarith only [h1, h13718, hlam]
                              · rcases p13696_3 (m.d 0 4) (by simp) with h13720 | h13720
                                · linarith only [h13720, h2, hlam]
                                · linarith only [h13290, h13720, hlam]
                          · linarith only [h13715, h3, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h0, hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h4, hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h7821, hlam, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h9029, hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h1, hlam, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h0, h13692, h13695, h4, hc12, hc34, hlam, hphi, ht23, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h9965, hlam, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h12966, hlam, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h2, hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13735 | h13735
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13736 | h13736
                            · linarith only [h13736, h7821, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13738 | h13738
                              · linarith only [h13738, h9965, hlam]
                              · linarith only [h13738, h4, hlam]
                          · linarith only [h0, h13735, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13742 | h13742
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13743 | h13743
                            · linarith only [h13743, h7821, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13745 | h13745
                              · linarith only [h13745, h9965, hlam]
                              · rcases p13696_3 (m.d 0 4) (by simp) with h13747 | h13747
                                · rcases p13696_3 (m.d 0 5) (by simp) with h13748 | h13748
                                  · linarith only [h13290, h13748, hlam]
                                  · linarith only [h12966, h13748, hlam]
                                · linarith only [h13747, h9965, hlam]
                          · linarith only [h1, h13742, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h13290, h13291, h13297, h13301, h7821, hc12, hc24, hlam, hphi, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h3, hlam, p13696_0]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13756 | h13756
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13757 | h13757
                            · linarith only [h13757, h9029, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13759 | h13759
                              · linarith only [h12966, h13759, hlam]
                              · linarith only [h13759, h4, hlam]
                          · linarith only [h0, h13756, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          rcases p13696_3 (m.d 0 1) (by simp) with h13763 | h13763
                          · rcases p13696_3 (m.d 0 2) (by simp) with h13764 | h13764
                            · linarith only [h13764, h9029, hlam]
                            · rcases p13696_3 (m.d 0 3) (by simp) with h13766 | h13766
                              · linarith only [h12966, h13766, hlam]
                              · rcases p13696_3 (m.d 0 4) (by simp) with h13768 | h13768
                                · rcases p13696_3 (m.d 0 5) (by simp) with h13769 | h13769
                                  · rcases h2bigk with h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c | h13770c
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13692, h13695, h4, hc12, hc34, hlam, hphi, ht23, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h4, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h7821, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h9029, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h0, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13291, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13293, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13295, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13692, h13695, hc02, hc34, hlam, hphi, ht23, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13692, h13695, hc12, hc34, hlam, hphi, ht23, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13690, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13692, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      rcases p13770_3 (m.d 0 2) (by simp) with h13786 | h13786
                                      · linarith only [h13786, hlam, p13770_0]
                                      · rcases p13770_3 (m.d 1 2) (by simp) with h13788 | h13788
                                        · linarith only [h13293, h13788, hlam]
                                        · rcases p13770_3 (m.d 2 3) (by simp) with h13790 | h13790
                                          · linarith only [h13690, h13790, hlam]
                                          · linarith only [h13790, h4, hlam]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      rcases p13770_3 (m.d 0 2) (by simp) with h13793 | h13793
                                      · linarith only [h13793, h7821, hlam]
                                      · linarith only [h0, h13793, hlam]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h0, h13690, h4, hc12, hc34, hlam, hphi, ht23, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h1, h13291, h13690, h9029, hc12, hc34, hlam, hphi, ht23, p13696_1, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      rcases p13770_3 (m.d 0 2) (by simp) with h13799 | h13799
                                      · linarith only [h13799, hlam, p13770_0]
                                      · rcases p13770_3 (m.d 1 2) (by simp) with h13801 | h13801
                                        · linarith only [h13295, h13801, hlam]
                                        · rcases p13770_3 (m.d 2 3) (by simp) with h13803 | h13803
                                          · linarith only [h13692, h13803, hlam]
                                          · linarith only [h13803, h4, hlam]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      rcases p13770_3 (m.d 0 2) (by simp) with h13806 | h13806
                                      · linarith only [h13806, h9029, hlam]
                                      · linarith only [h0, h13806, hlam]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p13770_1]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [h13694, hlam, p13770_0]
                                    · have p13770_0 := h13770c.1
                                      have p13770_1 := h13770c.2.1
                                      have p13770_2 := h13770c.2.2.1
                                      have p13770_3 := h13770c.2.2.2
                                      linarith only [hlam, p13770_0]
                                  · linarith only [h12966, h13769, hlam]
                                · linarith only [h13768, h9965, hlam]
                          · linarith only [h1, h13763, hlam]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [h13290, hlam, p13696_1]
                        · have p13696_0 := h13696c.1
                          have p13696_1 := h13696c.2.1
                          have p13696_2 := h13696c.2.2.1
                          have p13696_3 := h13696c.2.2.2
                          linarith only [hlam, p13696_0]
                      · linarith only [h13290, h13690, h13695, h7821, hlam]
                    · linarith only [h13290, h13694, h7821, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13819 | h13819
    · linarith only [h0, h13819, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13821 | h13821
      · linarith only [h0, h13821, h7821, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13823 | h13823
        · linarith only [h0, h13823, h9029, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13825 | h13825
          · linarith only [h1, h13825, h9965, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13827 | h13827
            · linarith only [h1, h12966, h13827, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13829 | h13829
              · linarith only [h13290, h13829, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13831 | h13831
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13832 | h13832
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13833 | h13833
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13834 | h13834
                      · linarith only [h13290, h13831, h13834, h4, h9965, hc02, hc23, hlam, hphi]
                      · linarith only [h0, h13833, h13834, h4, h9965, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13837 | h13837
                      · linarith only [h0, h13833, h13837, h7821, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c | h13839c
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          rcases p13839_3 (m.d 0 1) (by simp) with h13841 | h13841
                          · rcases p13839_3 (m.d 0 2) (by simp) with h13842 | h13842
                            · linarith only [h0, h13842, hlam]
                            · rcases p13839_3 (m.d 0 3) (by simp) with h13844 | h13844
                              · linarith only [h1, h13844, hlam]
                              · linarith only [h13844, h4, hlam]
                          · linarith only [h0, h13841, hlam]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          rcases p13839_3 (m.d 0 1) (by simp) with h13848 | h13848
                          · rcases p13839_3 (m.d 0 2) (by simp) with h13849 | h13849
                            · linarith only [h0, h13849, hlam]
                            · rcases p13839_3 (m.d 0 3) (by simp) with h13851 | h13851
                              · linarith only [h1, h13851, hlam]
                              · rcases p13839_3 (m.d 0 4) (by simp) with h13853 | h13853
                                · linarith only [h13853, h2, hlam]
                                · linarith only [h13853, h9965, hlam]
                          · linarith only [h1, h13848, hlam]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          rcases p13839_3 (m.d 0 1) (by simp) with h13857 | h13857
                          · rcases p13839_3 (m.d 0 2) (by simp) with h13858 | h13858
                            · linarith only [h0, h13858, hlam]
                            · rcases p13839_3 (m.d 0 3) (by simp) with h13860 | h13860
                              · linarith only [h1, h13860, hlam]
                              · rcases p13839_3 (m.d 0 4) (by simp) with h13862 | h13862
                                · linarith only [h13862, h2, hlam]
                                · rcases p13839_3 (m.d 0 5) (by simp) with h13864 | h13864
                                  · linarith only [h13864, h3, hlam]
                                  · linarith only [h13290, h13864, hlam]
                          · linarith only [h13857, h2, hlam]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          rcases p13839_3 (m.d 0 1) (by simp) with h13868 | h13868
                          · rcases p13839_3 (m.d 0 2) (by simp) with h13869 | h13869
                            · linarith only [h0, h13869, hlam]
                            · rcases p13839_3 (m.d 0 3) (by simp) with h13871 | h13871
                              · linarith only [h1, h13871, hlam]
                              · rcases p13839_3 (m.d 0 4) (by simp) with h13873 | h13873
                                · linarith only [h13873, h2, hlam]
                                · rcases p13839_3 (m.d 0 5) (by simp) with h13875 | h13875
                                  · linarith only [h13875, h3, hlam]
                                  · rcases h2bigk with h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c | h13877c
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13831, h4, h9965, hc12, hc24, hlam, hphi, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h4, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h7821, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h9029, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h0, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13819, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13821, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13823, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      rcases p13877_3 (m.d 0 2) (by simp) with h13888 | h13888
                                      · linarith only [h13888, hlam, p13877_0]
                                      · rcases p13877_3 (m.d 1 2) (by simp) with h13890 | h13890
                                        · linarith only [h13819, h13890, hlam]
                                        · rcases p13877_3 (m.d 2 3) (by simp) with h13892 | h13892
                                          · rcases p13877_3 (m.d 2 4) (by simp) with h13893 | h13893
                                            · linarith only [h13831, h13893, hlam]
                                            · linarith only [h13893, h7821, hlam]
                                          · linarith only [h13892, hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      rcases p13877_3 (m.d 0 2) (by simp) with h13897 | h13897
                                      · linarith only [h13897, h4, hlam]
                                      · linarith only [h0, h13897, hlam]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13831, h4, h9965, hc02, hc23, hlam, hphi, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h0, h9029, hc12, hc23, hlam, hphi, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h0, h13833, hc12, hc45, hlam, hphi, ht23, ht34, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13833, hc12, hc45, hlam, hphi, ht23, ht34, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13831, hlam, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [hlam, p13877_0]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13833, hlam, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      rcases p13877_3 (m.d 0 2) (by simp) with h13908 | h13908
                                      · linarith only [h13908, hlam, p13877_0]
                                      · rcases p13877_3 (m.d 1 2) (by simp) with h13910 | h13910
                                        · linarith only [h13823, h13910, hlam]
                                        · rcases p13877_3 (m.d 2 3) (by simp) with h13912 | h13912
                                          · rcases p13877_3 (m.d 2 4) (by simp) with h13913 | h13913
                                            · linarith only [h13833, h13913, hlam]
                                            · linarith only [h13913, h7821, hlam]
                                          · linarith only [h13912, h4, hlam]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      rcases p13877_3 (m.d 0 2) (by simp) with h13917 | h13917
                                      · linarith only [h13917, h9029, hlam]
                                      · linarith only [h0, h13917, hlam]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h13832, hlam, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [h0, h7821, hc12, hc25, hlam, hphi, p13877_1]
                                    · have p13877_0 := h13877c.1
                                      have p13877_1 := h13877c.2.1
                                      have p13877_2 := h13877c.2.2.1
                                      have p13877_3 := h13877c.2.2.2
                                      linarith only [hlam, p13877_0]
                          · linarith only [h13868, h3, hlam]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h4, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h7821, hlam, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h9029, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h1, hlam, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h9965, hc12, hc34, hlam, hphi, ht23, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h9965, hlam, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h12966, hlam, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h2, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h13290, hc12, hc45, hlam, hphi, ht23, ht34, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h13290, h4, hc12, hc45, hlam, hphi, ht23, ht34, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h13290, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h3, hlam, p13839_0]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h12966, h13832, hc12, hc23, hlam, hphi, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h12966, h13832, h4, hc12, hc23, hlam, hphi, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [h0, h12966, h13832, h7821, hc12, hc23, hlam, hphi, p13839_1]
                        · have p13839_0 := h13839c.1
                          have p13839_1 := h13839c.2.1
                          have p13839_2 := h13839c.2.2.1
                          have p13839_3 := h13839c.2.2.2
                          linarith only [hlam, p13839_0]
                  · linarith only [h0, h13831, h13832, h4, h9965, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13945 | h13945
                  · linarith only [h0, h12966, h13831, h13945, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13947 | h13947
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13948 | h13948
                      · rcases h0bigk with h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c | h13949c
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          rcases p13949_3 (m.d 0 1) (by simp) with h13951 | h13951
                          · rcases p13949_3 (m.d 0 2) (by simp) with h13952 | h13952
                            · linarith only [h0, h13952, hlam]
                            · rcases p13949_3 (m.d 0 3) (by simp) with h13954 | h13954
                              · linarith only [h1, h13954, hlam]
                              · linarith only [h13954, h4, hlam]
                          · linarith only [h0, h13951, hlam]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          rcases p13949_3 (m.d 0 1) (by simp) with h13958 | h13958
                          · rcases p13949_3 (m.d 0 2) (by simp) with h13959 | h13959
                            · linarith only [h0, h13959, hlam]
                            · rcases p13949_3 (m.d 0 3) (by simp) with h13961 | h13961
                              · linarith only [h1, h13961, hlam]
                              · rcases p13949_3 (m.d 0 4) (by simp) with h13963 | h13963
                                · linarith only [h13963, h2, hlam]
                                · linarith only [h13963, h9965, hlam]
                          · linarith only [h1, h13958, hlam]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          rcases p13949_3 (m.d 0 1) (by simp) with h13967 | h13967
                          · rcases p13949_3 (m.d 0 2) (by simp) with h13968 | h13968
                            · linarith only [h0, h13968, hlam]
                            · rcases p13949_3 (m.d 0 3) (by simp) with h13970 | h13970
                              · linarith only [h1, h13970, hlam]
                              · rcases p13949_3 (m.d 0 4) (by simp) with h13972 | h13972
                                · linarith only [h13972, h2, hlam]
                                · rcases p13949_3 (m.d 0 5) (by simp) with h13974 | h13974
                                  · linarith only [h13974, h3, hlam]
                                  · linarith only [h13290, h13974, hlam]
                          · linarith only [h13967, h2, hlam]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          rcases p13949_3 (m.d 0 1) (by simp) with h13978 | h13978
                          · rcases p13949_3 (m.d 0 2) (by simp) with h13979 | h13979
                            · linarith only [h0, h13979, hlam]
                            · rcases p13949_3 (m.d 0 3) (by simp) with h13981 | h13981
                              · linarith only [h1, h13981, hlam]
                              · rcases p13949_3 (m.d 0 4) (by simp) with h13983 | h13983
                                · linarith only [h13983, h2, hlam]
                                · rcases p13949_3 (m.d 0 5) (by simp) with h13985 | h13985
                                  · linarith only [h13985, h3, hlam]
                                  · rcases h2bigk with h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c | h13987c
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13945, h13948, h4, hc12, hc34, hlam, hphi, ht23, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h4, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h7821, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h9029, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h0, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13819, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13821, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13823, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13945, h13948, hc02, hc34, hlam, hphi, ht23, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13945, h13948, hc12, hc34, hlam, hphi, ht23, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13831, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13945, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      rcases p13987_3 (m.d 0 2) (by simp) with h14003 | h14003
                                      · linarith only [h14003, hlam, p13987_0]
                                      · rcases p13987_3 (m.d 1 2) (by simp) with h14005 | h14005
                                        · linarith only [h13821, h14005, hlam]
                                        · rcases p13987_3 (m.d 2 3) (by simp) with h14007 | h14007
                                          · linarith only [h13831, h14007, hlam]
                                          · linarith only [h14007, h4, hlam]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      rcases p13987_3 (m.d 0 2) (by simp) with h14010 | h14010
                                      · linarith only [h14010, h7821, hlam]
                                      · linarith only [h0, h14010, hlam]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h0, h13831, h4, hc12, hc34, hlam, hphi, ht23, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h0, h13831, h9029, hc12, hc34, hlam, hphi, ht23, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      rcases p13987_3 (m.d 0 2) (by simp) with h14016 | h14016
                                      · linarith only [h14016, hlam, p13987_0]
                                      · rcases p13987_3 (m.d 1 2) (by simp) with h14018 | h14018
                                        · linarith only [h13823, h14018, hlam]
                                        · rcases p13987_3 (m.d 2 3) (by simp) with h14020 | h14020
                                          · linarith only [h13945, h14020, hlam]
                                          · linarith only [h14020, h4, hlam]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      rcases p13987_3 (m.d 0 2) (by simp) with h14023 | h14023
                                      · linarith only [h14023, h9029, hlam]
                                      · linarith only [h0, h14023, hlam]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p13987_1]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [h13947, hlam, p13987_0]
                                    · have p13987_0 := h13987c.1
                                      have p13987_1 := h13987c.2.1
                                      have p13987_2 := h13987c.2.2.1
                                      have p13987_3 := h13987c.2.2.2
                                      linarith only [hlam, p13987_0]
                          · linarith only [h13978, h3, hlam]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h4, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h7821, hlam, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h9029, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h1, hlam, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, h13290, h9965, hc12, hc45, hlam, hphi, ht23, ht34, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h9965, hlam, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h12966, hlam, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h2, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, h13290, hc12, hc45, hlam, hphi, ht23, ht34, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h13290, hc03, hc45, hlam, hphi, ht34, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h13290, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h3, hlam, p13949_0]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, h13290, h13831, h13947, hc12, hc34, hlam, hphi, ht23, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, h13290, h13831, h13947, h4, hc12, hc34, hlam, hphi, ht23, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [h0, h13290, h13831, h13947, h7821, hc12, hc34, hlam, hphi, ht23, p13949_1]
                        · have p13949_0 := h13949c.1
                          have p13949_1 := h13949c.2.1
                          have p13949_2 := h13949c.2.2.1
                          have p13949_3 := h13949c.2.2.2
                          linarith only [hlam, p13949_0]
                      · linarith only [h13831, h13947, h13948, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14051 | h14051
                      · linarith only [h0, h13831, h13947, h14051, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h13831, h14051, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8178000 in
set_option maxHeartbeats 8178000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9965 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h7821 := hg7821
  have h9029 := hg9029
  rcases m.htr 0 3 5 (by decide) (by decide) with h12966 | h12966
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 h9965 h12966
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 h9965 h12966

set_option maxHeartbeats 8178000 in
set_option maxHeartbeats 8178000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h7821 := hg7821
  have h9029 := hg9029
  rcases m.htr 0 3 4 (by decide) (by decide) with h9965 | h9965
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 h9965
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 h9965

end R2N4
