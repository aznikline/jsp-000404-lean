import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S7
import Jsp000404.R1LeavesN7_9S8
import Jsp000404.R1LeavesN7_9S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4260 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h5319 | h5319
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5320 | h5320
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5321 | h5321
      · linarith only [h0, h4, h5321, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5323 | h5323
        · linarith only [h0, h3688, h5323, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5325 | h5325
          · linarith only [h1, h4260, h5325, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5327 | h5327
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5328 | h5328
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5329 | h5329
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5330 | h5330
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5331 | h5331
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5332 | h5332
                      · rcases h3bigk with h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c | h5333c
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h4260, h5327, h5332, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h4, hlam, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h4260, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h4260, h5329, h5332, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h1, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5321, hlam, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5325, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h1, h4260, h5329, h5332, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          rcases p5333_3 (m.d 0 3) (by simp) with h5344 | h5344
                          · linarith only [h4, h5344, hlam]
                          · rcases p5333_3 (m.d 1 3) (by simp) with h5346 | h5346
                            · linarith only [h5321, h5346, hlam]
                            · rcases p5333_3 (m.d 2 3) (by simp) with h5348 | h5348
                              · rcases p5333_3 (m.d 3 4) (by simp) with h5349 | h5349
                                · linarith only [h5329, h5349, hlam]
                                · linarith only [h4260, h5349, hlam]
                              · linarith only [h4, h5348, hlam]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          rcases p5333_3 (m.d 0 3) (by simp) with h5353 | h5353
                          · linarith only [h4, h5353, hlam]
                          · linarith only [h1, h5353, hlam]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h4, h4260, hc02, hc23, hlam, hphi, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h1, h4260, h5327, h5329, hlam, p5333_2]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h1, h5327, h5329, h5332, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5327, h5329, h5332, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5333_1]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5329, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          rcases p5333_3 (m.d 0 3) (by simp) with h5363 | h5363
                          · linarith only [h4260, h5363, hlam]
                          · linarith only [h5319, h5363, hlam]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5319, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5327, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5330, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [h5332, hlam, p5333_0]
                        · have p5333_0 := h5333c.1
                          have p5333_1 := h5333c.2.1
                          have p5333_2 := h5333c.2.2.1
                          have p5333_3 := h5333c.2.2.2
                          linarith only [hlam, p5333_0]
                      · linarith only [h4260, h5320, h5332, hlam]
                    · linarith only [h0, h1, h3688, h4260, h5327, h5328, h5331, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h4260, h5329, h5330, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5374 | h5374
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5375 | h5375
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5376 | h5376
                      · rcases h3bigk with h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c | h5377c
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h4, h5329, hc13, hc34, hlam, hphi, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h4, hlam, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h4260, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5382 | h5382
                          · rcases p5377_3 (m.d 1 3) (by simp) with h5383 | h5383
                            · linarith only [h1, h5383, hlam]
                            · linarith only [h5327, h5383, hlam]
                          · linarith only [h5382, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h1, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5321, hlam, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5325, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5391 | h5391
                          · rcases p5377_3 (m.d 1 3) (by simp) with h5392 | h5392
                            · rcases p5377_3 (m.d 2 3) (by simp) with h5393 | h5393
                              · rcases p5377_3 (m.d 3 4) (by simp) with h5394 | h5394
                                · rcases p5377_3 (m.d 3 5) (by simp) with h5395 | h5395
                                  · linarith only [h5395, hlam, p5377_0]
                                  · rcases h4bigk with h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c | h5397c
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h3688, h5323, h5329, hc12, hc34, hlam, hphi, ht23, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h3688, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h4260, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      rcases p5397_3 (m.d 0 4) (by simp) with h5402 | h5402
                                      · rcases p5397_3 (m.d 1 4) (by simp) with h5403 | h5403
                                        · linarith only [h2, h5403, hlam]
                                        · linarith only [h5328, h5403, hlam]
                                      · linarith only [h5402, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h2, hlam, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5323, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5325, hlam, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h3688, h5329, hc02, hc34, hlam, hphi, ht23, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5323, h5329, hc12, hc34, hlam, hphi, ht23, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5329, hlam, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      rcases p5397_3 (m.d 0 4) (by simp) with h5416 | h5416
                                      · linarith only [h3688, h5416, hlam]
                                      · linarith only [h5320, h5416, hlam]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h1, h4260, h5376, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5377_1, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5325, h5376, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5377_1, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h0, h3688, hc12, hc34, hlam, hphi, ht23, p5397_1]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      rcases p5397_3 (m.d 0 4) (by simp) with h5423 | h5423
                                      · linarith only [h4260, h5423, hlam]
                                      · linarith only [h5320, h5423, hlam]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5320, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5328, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5375, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [h5376, hlam, p5397_0]
                                    · have p5397_0 := h5397c.1
                                      have p5397_1 := h5397c.2.1
                                      have p5397_2 := h5397c.2.2.1
                                      have p5397_3 := h5397c.2.2.2
                                      linarith only [hlam, p5397_0]
                                · linarith only [h5376, h5394, hlam]
                              · linarith only [h5374, h5393, hlam]
                            · linarith only [h5392, hlam, p5377_0]
                          · linarith only [h5319, h5391, hlam]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5329, hc03, hc34, hlam, hphi, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5329, hc13, hc34, hlam, hphi, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5329, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5439 | h5439
                          · linarith only [h4, h5439, hlam]
                          · linarith only [h5319, h5439, hlam]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5442 | h5442
                          · linarith only [h5442, hlam, p5377_0]
                          · rcases p5377_3 (m.d 1 3) (by simp) with h5444 | h5444
                            · linarith only [h5325, h5444, hlam]
                            · rcases p5377_3 (m.d 2 3) (by simp) with h5446 | h5446
                              · linarith only [h5329, h5446, hlam]
                              · linarith only [h4, h5446, hlam]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5449 | h5449
                          · linarith only [h4260, h5449, hlam]
                          · linarith only [h1, h5449, hlam]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p5377_1]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          rcases p5377_3 (m.d 0 3) (by simp) with h5454 | h5454
                          · linarith only [h4260, h5454, hlam]
                          · linarith only [h5319, h5454, hlam]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5319, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5327, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5374, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [h5376, hlam, p5377_0]
                        · have p5377_0 := h5377c.1
                          have p5377_1 := h5377c.2.1
                          have p5377_2 := h5377c.2.2.1
                          have p5377_3 := h5377c.2.2.2
                          linarith only [hlam, p5377_0]
                      · linarith only [h1, h4260, h5320, h5327, h5376, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h2, h4, h5328, h5329, h5375, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h0, h1, h4, h5327, h5374, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h5325, h5327, h5328, hlam]
            · linarith only [h4260, h5319, h5327, hc13, hc34, hlam, hphi]
    · linarith only [h4260, h5319, h5320, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5468 | h5468
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5469 | h5469
      · linarith only [h0, h4, h5469, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5471 | h5471
        · linarith only [h0, h3688, h5471, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5473 | h5473
          · linarith only [h1, h4260, h5473, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5475 | h5475
            · linarith only [h1, h5319, h5475, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5477 | h5477
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5478 | h5478
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5479 | h5479
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5480 | h5480
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5481 | h5481
                      · rcases h3bigk with h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h4260, h5478, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h4, hlam, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h4260, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5319, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5469, hlam, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5473, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5475, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          rcases p5482_3 (m.d 0 3) (by simp) with h5493 | h5493
                          · linarith only [h4, h5493, hlam]
                          · rcases p5482_3 (m.d 1 3) (by simp) with h5495 | h5495
                            · linarith only [h5469, h5495, hlam]
                            · rcases p5482_3 (m.d 2 3) (by simp) with h5497 | h5497
                              · rcases p5482_3 (m.d 3 4) (by simp) with h5498 | h5498
                                · linarith only [h5478, h5498, hlam]
                                · linarith only [h4260, h5498, hlam]
                              · linarith only [h4, h5497, hlam]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          rcases p5482_3 (m.d 0 3) (by simp) with h5502 | h5502
                          · linarith only [h4, h5502, hlam]
                          · linarith only [h1, h5502, hlam]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, h4260, h5469, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, h5319, h5469, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, h5469, h5478, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5469, h5478, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5478, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, h5319, h5469, h5478, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h1, h5469, h5479, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5469, h5479, hc12, hc23, hlam, hphi, p5482_1]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5479, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [h5481, hlam, p5482_0]
                        · have p5482_0 := h5482c.1
                          have p5482_1 := h5482c.2.1
                          have p5482_2 := h5482c.2.2.1
                          have p5482_3 := h5482c.2.2.2
                          linarith only [hlam, p5482_0]
                      · linarith only [h1, h2, h4260, h5469, h5477, h5481, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h2, h4260, h5477, h5478, h5480, hlam]
                  · linarith only [h1, h4260, h5469, h5478, h5479, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5521 | h5521
                  · linarith only [h1, h5319, h5469, h5478, h5521, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5523 | h5523
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5524 | h5524
                      · rcases h3bigk with h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c | h5525c
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h4, h5469, h5521, h5524, hc12, hc34, hlam, hphi, ht23, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h4, hlam, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h4260, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5319, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h1, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5469, hlam, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5473, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5475, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5521, h5524, hc03, hc34, hlam, hphi, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5469, h5521, h5524, hc12, hc34, hlam, hphi, ht23, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5478, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5521, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          rcases p5525_3 (m.d 0 3) (by simp) with h5541 | h5541
                          · linarith only [h5541, hlam, p5525_0]
                          · rcases p5525_3 (m.d 1 3) (by simp) with h5543 | h5543
                            · linarith only [h5473, h5543, hlam]
                            · rcases p5525_3 (m.d 2 3) (by simp) with h5545 | h5545
                              · linarith only [h5478, h5545, hlam]
                              · linarith only [h4, h5545, hlam]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          rcases p5525_3 (m.d 0 3) (by simp) with h5548 | h5548
                          · linarith only [h4260, h5548, hlam]
                          · linarith only [h1, h5548, hlam]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h1, h5319, h5469, hc12, hc34, hlam, hphi, ht23, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          rcases p5525_3 (m.d 0 3) (by simp) with h5554 | h5554
                          · linarith only [h5554, hlam, p5525_0]
                          · rcases p5525_3 (m.d 1 3) (by simp) with h5556 | h5556
                            · linarith only [h5475, h5556, hlam]
                            · rcases p5525_3 (m.d 2 3) (by simp) with h5558 | h5558
                              · linarith only [h5521, h5558, hlam]
                              · linarith only [h4, h5558, hlam]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          rcases p5525_3 (m.d 0 3) (by simp) with h5561 | h5561
                          · linarith only [h5319, h5561, hlam]
                          · linarith only [h1, h5561, hlam]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p5525_1]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [h5524, hlam, p5525_0]
                        · have p5525_0 := h5525c.1
                          have p5525_1 := h5525c.2.1
                          have p5525_2 := h5525c.2.2.1
                          have p5525_3 := h5525c.2.2.2
                          linarith only [hlam, p5525_0]
                      · linarith only [h0, h2, h3688, h5477, h5478, h5524, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h3688, h5468, h5523, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5569 | h5569
                · linarith only [h4260, h5468, h5469, h5473, h5477, h5569, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5571 | h5571
                  · linarith only [h1, h5319, h5469, h5569, h5571, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5573 | h5573
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5574 | h5574
                      · rcases h3bigk with h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c | h5575c
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h4, h5469, h5571, h5574, hc12, hc34, hlam, hphi, ht23, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h4, hlam, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h4260, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5319, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h1, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5469, hlam, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5473, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5475, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5571, h5574, hc03, hc34, hlam, hphi, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5469, h5571, h5574, hc12, hc34, hlam, hphi, ht23, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5569, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5571, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          rcases p5575_3 (m.d 0 3) (by simp) with h5591 | h5591
                          · linarith only [h5591, hlam, p5575_0]
                          · rcases p5575_3 (m.d 1 3) (by simp) with h5593 | h5593
                            · linarith only [h5473, h5593, hlam]
                            · rcases p5575_3 (m.d 2 3) (by simp) with h5595 | h5595
                              · linarith only [h5569, h5595, hlam]
                              · linarith only [h4, h5595, hlam]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          rcases p5575_3 (m.d 0 3) (by simp) with h5598 | h5598
                          · linarith only [h4260, h5598, hlam]
                          · linarith only [h1, h5598, hlam]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h1, h5319, h5469, hc12, hc34, hlam, hphi, ht23, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          rcases p5575_3 (m.d 0 3) (by simp) with h5604 | h5604
                          · linarith only [h5604, hlam, p5575_0]
                          · rcases p5575_3 (m.d 1 3) (by simp) with h5606 | h5606
                            · linarith only [h5475, h5606, hlam]
                            · rcases p5575_3 (m.d 2 3) (by simp) with h5608 | h5608
                              · linarith only [h5571, h5608, hlam]
                              · linarith only [h4, h5608, hlam]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          rcases p5575_3 (m.d 0 3) (by simp) with h5611 | h5611
                          · linarith only [h5319, h5611, hlam]
                          · linarith only [h1, h5611, hlam]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p5575_1]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [h5574, hlam, p5575_0]
                        · have p5575_0 := h5575c.1
                          have p5575_1 := h5575c.2.1
                          have p5575_2 := h5575c.2.2.1
                          have p5575_3 := h5575c.2.2.2
                          linarith only [hlam, p5575_0]
                      · linarith only [h1, h3688, h4260, h5468, h5469, h5574, hc12, hc24, hlam, hphi]
                    · linarith only [h3688, h5468, h5573, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5619 | h5619
      · linarith only [h0, h4, h5619, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5621 | h5621
        · linarith only [h0, h3688, h5621, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5623 | h5623
          · linarith only [h1, h4260, h5623, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5625 | h5625
            · linarith only [h1, h5319, h5625, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5627 | h5627
              · linarith only [h2, h5468, h5627, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5629 | h5629
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5630 | h5630
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5631 | h5631
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5632 | h5632
                      · linarith only [h0, h3688, h5468, h5629, h5632, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h4, h4260, h5631, h5632, hc12, hc24, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5635 | h5635
                      · linarith only [h0, h3688, h5631, h5635, hc12, hc34, hlam, hphi, ht23]
                      · rcases h3bigk with h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c | h5637c
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h4260, hc13, hc34, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h4, hlam, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h4260, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5319, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h1, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5619, hlam, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5623, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5625, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          rcases p5637_3 (m.d 0 3) (by simp) with h5648 | h5648
                          · linarith only [h4, h5648, hlam]
                          · rcases p5637_3 (m.d 1 3) (by simp) with h5650 | h5650
                            · linarith only [h5619, h5650, hlam]
                            · rcases p5637_3 (m.d 2 3) (by simp) with h5652 | h5652
                              · rcases p5637_3 (m.d 3 4) (by simp) with h5653 | h5653
                                · linarith only [h5629, h5653, hlam]
                                · linarith only [h4260, h5653, hlam]
                              · linarith only [h4, h5652, hlam]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          rcases p5637_3 (m.d 0 3) (by simp) with h5657 | h5657
                          · linarith only [h4, h5657, hlam]
                          · linarith only [h1, h5657, hlam]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h4, h4260, hc02, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h0, h4, h5319, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h0, h4, h5629, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5619, h5629, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5629, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5635, hlam, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h0, h4, h5630, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5619, h5630, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h5630, hlam, p5637_0]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [h0, h4, h4260, h5630, hc12, hc23, hlam, hphi, p5637_1]
                        · have p5637_0 := h5637c.1
                          have p5637_1 := h5637c.2.1
                          have p5637_2 := h5637c.2.2.1
                          have p5637_3 := h5637c.2.2.2
                          linarith only [hlam, p5637_0]
                  · linarith only [h0, h4, h4260, h5629, h5630, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5674 | h5674
                  · linarith only [h0, h4, h5319, h5629, h5674, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5676 | h5676
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5677 | h5677
                      · rcases h3bigk with h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h4260, h5468, h5619, h5676, hc12, hc24, hlam, hphi, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h4, hlam, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h4260, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5319, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h1, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5619, hlam, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5623, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5625, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5674, h5677, hc03, hc34, hlam, hphi, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5619, h5674, h5677, hc12, hc34, hlam, hphi, ht23, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5629, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5674, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          rcases p5678_3 (m.d 0 3) (by simp) with h5694 | h5694
                          · linarith only [h5694, hlam, p5678_0]
                          · rcases p5678_3 (m.d 1 3) (by simp) with h5696 | h5696
                            · linarith only [h5623, h5696, hlam]
                            · rcases p5678_3 (m.d 2 3) (by simp) with h5698 | h5698
                              · linarith only [h5629, h5698, hlam]
                              · linarith only [h4, h5698, hlam]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          rcases p5678_3 (m.d 0 3) (by simp) with h5701 | h5701
                          · linarith only [h4260, h5701, hlam]
                          · linarith only [h1, h5701, hlam]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h1, h5319, h5619, hc12, hc34, hlam, hphi, ht23, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          rcases p5678_3 (m.d 0 3) (by simp) with h5707 | h5707
                          · linarith only [h5707, hlam, p5678_0]
                          · rcases p5678_3 (m.d 1 3) (by simp) with h5709 | h5709
                            · linarith only [h5625, h5709, hlam]
                            · rcases p5678_3 (m.d 2 3) (by simp) with h5711 | h5711
                              · linarith only [h5674, h5711, hlam]
                              · linarith only [h4, h5711, hlam]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          rcases p5678_3 (m.d 0 3) (by simp) with h5714 | h5714
                          · linarith only [h5319, h5714, hlam]
                          · linarith only [h1, h5714, hlam]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p5678_1]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [h5677, hlam, p5678_0]
                        · have p5678_0 := h5678c.1
                          have p5678_1 := h5678c.2.1
                          have p5678_2 := h5678c.2.2.1
                          have p5678_3 := h5678c.2.2.2
                          linarith only [hlam, p5678_0]
                      · linarith only [h5629, h5676, h5677, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5721 | h5721
                      · linarith only [h0, h4, h5629, h5676, h5721, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h4, h5629, h5721, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3688 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h4260 | h4260
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x0 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1_x1 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688 h4260

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h3688 | h3688
  · exact r1l7_13_24_L_I_H_I_s3_x1_x0 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688
  · exact r1l7_13_24_L_I_H_I_s3_x1_x1 m hb3 hb4 hg0 hg1 hg2 hg3 h4 h3688

set_option maxHeartbeats 11440000 in
set_option maxHeartbeats 11440000 in
theorem r1l7_13_24_L_I_H_I_s3 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_13_24_L_I_H_I_s3_x0 m hb3 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_13_24_L_I_H_I_s3_x1 m hb3 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 11672000 in
set_option maxHeartbeats 11672000 in
theorem r1l7_13_24_L_I_H_I_s2 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_13_24_L_I_H_I_s3 m hb3 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5724 | h5724
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5725 | h5725
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5726 | h5726
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5727 | h5727
          · linarith only [h1, h3, h5727, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5729 | h5729
            · linarith only [h2, h3, h5729, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5731 | h5731
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5732 | h5732
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5733 | h5733
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5734 | h5734
                    · linarith only [h1, h3, h5727, h5734, hlam]
                    · linarith only [h0, h3, h5731, h5734, hc23, hc35, hlam, hphi]
                  · linarith only [h5726, h5727, h5733, hc13, hc35, hlam, hphi]
                · linarith only [h0, h3, h5725, h5731, h5732, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5739 | h5739
                · linarith only [h0, h3, h5724, h5731, h5739, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5741 | h5741
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5742 | h5742
                    · linarith only [h1, h3, h5727, h5742, hlam]
                    · linarith only [h0, h3, h5724, h5731, h5742, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h5726, h5727, h5741, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5746 | h5746
          · linarith only [h1, h3, h5746, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5748 | h5748
            · linarith only [h0, h3, h5725, h5748, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5750 | h5750
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5751 | h5751
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5752 | h5752
                  · linarith only [h1, h3, h5726, h5752, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5754 | h5754
                    · linarith only [h1, h3, h5746, h5754, hlam]
                    · linarith only [h0, h3, h5750, h5754, hc23, hc35, hlam, hphi]
                · linarith only [h0, h3, h5725, h5750, h5751, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5758 | h5758
                · linarith only [h0, h3, h5724, h5750, h5758, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5760 | h5760
                  · linarith only [h1, h3, h5726, h5760, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5762 | h5762
                    · linarith only [h1, h3, h5746, h5762, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h3, h5724, h5750, h5762, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5765 | h5765
        · linarith only [h5724, h5725, h5765, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5767 | h5767
          · linarith only [h0, h3, h5724, h5767, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5769 | h5769
            · linarith only [h2, h3, h5769, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5771 | h5771
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5772 | h5772
                · linarith only [h0, h5725, h5772, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5774 | h5774
                  · linarith only [h1, h5765, h5774, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5776 | h5776
                    · linarith only [h1, h2, h3, h5724, h5725, h5767, h5772, h5776, hc12, hc24, hlam, hphi]
                    · linarith only [h2, h3, h5771, h5772, h5776, hc23, hc35, hlam, hphi]
              · linarith only [h5724, h5725, h5769, h5771, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5780 | h5780
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5781 | h5781
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5782 | h5782
          · linarith only [h1, h3, h5782, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5784 | h5784
            · linarith only [h1, h3, h5724, h5780, h5784, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5786 | h5786
              · linarith only [h0, h3, h5724, h5780, h5786, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5788 | h5788
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5789 | h5789
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5790 | h5790
                    · linarith only [h1, h3, h5782, h5790, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5792 | h5792
                      · linarith only [h0, h2, h3, h5724, h5780, h5784, h5792, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h3, h5788, h5792, hc24, hc45, hlam, hphi]
                  · linarith only [h1, h3, h5781, h5786, h5788, h5789, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h5724, h5780, h5782, h5788, hc12, hc35, hlam, hphi, ht23]
        · linarith only [h5724, h5780, h5781, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5798 | h5798
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5799 | h5799
          · linarith only [h1, h3, h5799, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5801 | h5801
            · linarith only [h1, h3, h5798, h5801, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5803 | h5803
              · linarith only [h0, h5724, h5803, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5805 | h5805
                · linarith only [h0, h3, h5780, h5805, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5807 | h5807
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5808 | h5808
                    · linarith only [h1, h3, h5799, h5808, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5810 | h5810
                      · linarith only [h2, h3, h5801, h5808, h5810, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h3, h5807, h5810, hc34, hc45, hlam, hphi]
                  · linarith only [h5798, h5799, h5807, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5814 | h5814
          · linarith only [h1, h3, h5814, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5816 | h5816
            · linarith only [h2, h3, h5816, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5818 | h5818
              · linarith only [h0, h5724, h5818, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5820 | h5820
                · linarith only [h1, h5780, h5798, h5818, h5820, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h5822 | h5822
                  · linarith only [h1, h5798, h5822, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h5824 | h5824
                    · linarith only [h0, h1, h3, h5798, h5814, h5824, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h5826 | h5826
                      · linarith only [h2, h3, h5798, h5816, h5824, h5826, hc03, hc35, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h5828 | h5828
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5829 | h5829
                          · linarith only [h2, h3, h5818, h5822, h5824, h5829, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h5724, h5798, h5828, h5829, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h5832 | h5832
                          · linarith only [h0, h5724, h5814, h5828, h5832, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h5834 | h5834
                            · linarith only [h2, h3, h5818, h5822, h5826, h5834, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h5836 | h5836
                              · linarith only [h0, h5724, h5828, h5834, h5836, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h5724, h5828, h5836, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 12170000 in
set_option maxHeartbeats 12170000 in
theorem r1l7_13_24_L_I_H_I_s1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_13_24_L_I_H_I_s2 m hb3 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h5839 | h5839
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5840 | h5840
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5841 | h5841
        · linarith only [h0, h2, h5841, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5843 | h5843
          · linarith only [h1, h2, h5843, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5845 | h5845
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5846 | h5846
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5847 | h5847
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5848 | h5848
                  · linarith only [h0, h2, h5841, h5848, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5850 | h5850
                    · linarith only [h1, h2, h5843, h5850, hlam]
                    · linarith only [h0, h2, h5847, h5850, hc23, hc34, hlam, hphi]
                · linarith only [h5840, h5841, h5847, hc12, hc24, hlam, hphi]
              · linarith only [h1, h2, h5845, h5846, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5855 | h5855
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5856 | h5856
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5857 | h5857
                  · linarith only [h0, h2, h5841, h5857, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5859 | h5859
                    · linarith only [h0, h2, h5843, h5856, h5857, h5859, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h2, h5856, h5859, hc23, hc34, hlam, hphi]
                · linarith only [h5840, h5841, h5856, hc12, hc24, hlam, hphi]
              · linarith only [h2, h5839, h5855, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5864 | h5864
        · linarith only [h1, h2, h5840, h5864, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5866 | h5866
          · linarith only [h1, h2, h5866, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5868 | h5868
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5869 | h5869
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5870 | h5870
                · linarith only [h0, h2, h5840, h5870, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5872 | h5872
                  · linarith only [h0, h2, h5864, h5872, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5874 | h5874
                    · linarith only [h1, h2, h5840, h5866, h5872, h5874, hc02, hc24, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5876 | h5876
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5877 | h5877
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5878 | h5878
                          · linarith only [h1, h2, h5874, h5876, h5878, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5880 | h5880
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5881 | h5881
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5882 | h5882
                                · rcases h3bigk with h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c | h5883c
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h1, h2, h5876, h5882, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5840, hlam, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5866, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    rcases p5883_3 (m.d 0 3) (by simp) with h5888 | h5888
                                    · rcases p5883_3 (m.d 1 3) (by simp) with h5889 | h5889
                                      · linarith only [h1, h5889, hlam]
                                      · linarith only [h5876, h5889, hlam]
                                    · linarith only [h5888, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h1, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5870, hlam, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5874, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h1, h2, h5872, h5878, h5882, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5878, hc03, hc34, hlam, hphi, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5878, hc13, hc34, hlam, hphi, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5878, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    rcases p5883_3 (m.d 0 3) (by simp) with h5902 | h5902
                                    · linarith only [h5840, h5902, hlam]
                                    · linarith only [h5868, h5902, hlam]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    rcases p5883_3 (m.d 0 3) (by simp) with h5905 | h5905
                                    · linarith only [h5905, hlam, p5883_0]
                                    · rcases p5883_3 (m.d 1 3) (by simp) with h5907 | h5907
                                      · linarith only [h5874, h5907, hlam]
                                      · rcases p5883_3 (m.d 2 3) (by simp) with h5909 | h5909
                                        · linarith only [h5878, h5909, hlam]
                                        · linarith only [h5840, h5909, hlam]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    rcases p5883_3 (m.d 0 3) (by simp) with h5912 | h5912
                                    · linarith only [h5866, h5912, hlam]
                                    · linarith only [h1, h5912, hlam]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h0, h5840, hc12, hc34, hlam, hphi, ht23, p5883_1]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h1, h2, h5872, h5876, h5878, hlam, p5883_2]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5868, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5876, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5880, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [h5882, hlam, p5883_0]
                                  · have p5883_0 := h5883c.1
                                    have p5883_1 := h5883c.2.1
                                    have p5883_2 := h5883c.2.2.1
                                    have p5883_3 := h5883c.2.2.2
                                    linarith only [hlam, p5883_0]
                                · linarith only [h1, h2, h5872, h5878, h5882, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h1, h2, h5872, h5876, h5877, h5881, hlam]
                            · linarith only [h0, h1, h5840, h5876, h5880, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h2, h5877, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h1, h2, h5868, h5870, h5874, h5876, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h2, h5868, h5869, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5929 | h5929
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5930 | h5930
                · linarith only [h0, h5840, h5930, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5932 | h5932
                  · linarith only [h0, h5864, h5932, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5934 | h5934
                    · linarith only [h1, h5866, h5934, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5936 | h5936
                      · linarith only [h1, h5868, h5936, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5938 | h5938
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5939 | h5939
                          · linarith only [h0, h2, h5934, h5939, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5941 | h5941
                            · linarith only [h0, h5840, h5868, h5939, h5941, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5943 | h5943
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5944 | h5944
                                · rcases h3bigk with h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c | h5945c
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5840, h5930, h5941, h5944, hc12, hc34, hlam, hphi, ht23, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5840, hlam, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5866, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5868, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h1, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5930, hlam, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5934, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5936, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5941, h5944, hc03, hc34, hlam, hphi, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5930, h5941, h5944, hc12, hc34, hlam, hphi, ht23, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5939, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5941, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    rcases p5945_3 (m.d 0 3) (by simp) with h5961 | h5961
                                    · linarith only [h5961, hlam, p5945_0]
                                    · rcases p5945_3 (m.d 1 3) (by simp) with h5963 | h5963
                                      · linarith only [h5934, h5963, hlam]
                                      · rcases p5945_3 (m.d 2 3) (by simp) with h5965 | h5965
                                        · linarith only [h5939, h5965, hlam]
                                        · linarith only [h5840, h5965, hlam]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    rcases p5945_3 (m.d 0 3) (by simp) with h5968 | h5968
                                    · linarith only [h5866, h5968, hlam]
                                    · linarith only [h1, h5968, hlam]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h0, h5840, hc12, hc34, hlam, hphi, ht23, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h1, h5868, h5930, hc12, hc34, hlam, hphi, ht23, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    rcases p5945_3 (m.d 0 3) (by simp) with h5974 | h5974
                                    · linarith only [h5974, hlam, p5945_0]
                                    · rcases p5945_3 (m.d 1 3) (by simp) with h5976 | h5976
                                      · linarith only [h5936, h5976, hlam]
                                      · rcases p5945_3 (m.d 2 3) (by simp) with h5978 | h5978
                                        · linarith only [h5941, h5978, hlam]
                                        · linarith only [h5840, h5978, hlam]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    rcases p5945_3 (m.d 0 3) (by simp) with h5981 | h5981
                                    · linarith only [h5868, h5981, hlam]
                                    · linarith only [h1, h5981, hlam]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h0, h5840, hc12, hc35, hlam, hphi, ht23, p5945_1]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [h5944, hlam, p5945_0]
                                  · have p5945_0 := h5945c.1
                                    have p5945_1 := h5945c.2.1
                                    have p5945_2 := h5945c.2.2.1
                                    have p5945_3 := h5945c.2.2.2
                                    linarith only [hlam, p5945_0]
                                · linarith only [h5864, h5929, h5939, h5944, hlam]
                              · linarith only [h2, h5839, h5932, h5938, h5943, hlam]
                        · linarith only [h2, h5839, h5930, h5936, h5938, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h2, h5839, h5929, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5991 | h5991
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5992 | h5992
        · linarith only [h0, h2, h5992, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5994 | h5994
          · linarith only [h1, h2, h5994, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5996 | h5996
            · linarith only [h0, h5839, h5991, h5996, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5998 | h5998
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5999 | h5999
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6000 | h6000
                  · linarith only [h0, h2, h5992, h6000, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6002 | h6002
                    · linarith only [h0, h1, h5839, h5991, h5994, h5998, h6002, hlam]
                    · linarith only [h0, h2, h5999, h6002, hc23, hc34, hlam, hphi]
                · linarith only [h5991, h5992, h5999, hc12, hc24, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6006 | h6006
                · linarith only [h0, h2, h5998, h6006, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h2, h5991, h5998, h6006, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h6009 | h6009
        · linarith only [h1, h2, h5991, h6009, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6011 | h6011
          · linarith only [h1, h2, h6011, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6013 | h6013
            · linarith only [h1, h5839, h6013, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6015 | h6015
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6016 | h6016
                · linarith only [h0, h2, h5991, h6016, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6018 | h6018
                  · linarith only [h1, h5839, h6009, h6015, h6016, h6018, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6020 | h6020
                    · linarith only [h1, h5839, h6011, h6015, h6020, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6022 | h6022
                      · linarith only [h1, h2, h5991, h6013, h6020, h6022, hc02, hc34, hlam, hphi, ht23]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6024 | h6024
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6025 | h6025
                          · linarith only [h0, h5839, h6020, h6024, h6025, hc12, hc23, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6027 | h6027
                            · linarith only [h1, h5839, h6016, h6022, h6025, h6027, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6029 | h6029
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6030 | h6030
                                · rcases h3bigk with h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c | h6031c
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h1, h5839, h6016, h6018, h6024, hc12, hc24, hlam, hphi, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h5991, hlam, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6011, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6013, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h1, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6016, hlam, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6020, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6022, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6027, h6030, hc03, hc34, hlam, hphi, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6016, h6027, h6030, hc12, hc34, hlam, hphi, ht23, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6025, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6027, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    rcases p6031_3 (m.d 0 3) (by simp) with h6047 | h6047
                                    · linarith only [h6047, hlam, p6031_0]
                                    · rcases p6031_3 (m.d 1 3) (by simp) with h6049 | h6049
                                      · linarith only [h6020, h6049, hlam]
                                      · rcases p6031_3 (m.d 2 3) (by simp) with h6051 | h6051
                                        · linarith only [h6025, h6051, hlam]
                                        · linarith only [h5991, h6051, hlam]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    rcases p6031_3 (m.d 0 3) (by simp) with h6054 | h6054
                                    · linarith only [h6011, h6054, hlam]
                                    · linarith only [h1, h6054, hlam]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h0, h5991, hc12, hc34, hlam, hphi, ht23, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h1, h6013, h6016, hc12, hc34, hlam, hphi, ht23, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    rcases p6031_3 (m.d 0 3) (by simp) with h6060 | h6060
                                    · linarith only [h6060, hlam, p6031_0]
                                    · rcases p6031_3 (m.d 1 3) (by simp) with h6062 | h6062
                                      · linarith only [h6022, h6062, hlam]
                                      · rcases p6031_3 (m.d 2 3) (by simp) with h6064 | h6064
                                        · linarith only [h6027, h6064, hlam]
                                        · linarith only [h5991, h6064, hlam]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    rcases p6031_3 (m.d 0 3) (by simp) with h6067 | h6067
                                    · linarith only [h6013, h6067, hlam]
                                    · linarith only [h1, h6067, hlam]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h0, h5991, hc12, hc35, hlam, hphi, ht23, p6031_1]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [h6030, hlam, p6031_0]
                                  · have p6031_0 := h6031c.1
                                    have p6031_1 := h6031c.2.1
                                    have p6031_2 := h6031c.2.2.1
                                    have p6031_3 := h6031c.2.2.2
                                    linarith only [hlam, p6031_0]
                                · linarith only [h0, h5839, h6015, h6018, h6024, h6025, h6030, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h2, h6015, h6018, h6029, hlam]
                        · linarith only [h2, h6015, h6024, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6076 | h6076
                · linarith only [h0, h5991, h6076, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6078 | h6078
                  · linarith only [h0, h2, h6015, h6078, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6080 | h6080
                    · linarith only [h1, h2, h6015, h6080, hc34, hc45, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6082 | h6082
                      · linarith only [h1, h2, h5991, h6013, h6015, h6082, hc02, hc45, hlam, hphi, ht23, ht34]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6084 | h6084
                        · linarith only [h0, h2, h6015, h6080, h6084, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h2, h6076, h6084, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 14718000 in
set_option maxHeartbeats 14718000 in
theorem r1l7_13_24_L_I_H_I_s0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  exact r1l7_13_24_L_I_H_I_s1 m hb3 hb4 h0 h1

end R2N4
