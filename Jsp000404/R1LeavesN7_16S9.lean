import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12272000 in
set_option maxHeartbeats 12272000 in
theorem r1l7_21_15_H_I_L_I_s0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1emin := hb1.2.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_15_H_I_L_I_s1 m hb1 hb5 h0 h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h5385 | h5385
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5386 | h5386
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5387 | h5387
        · linarith only [h0, h1, h5387, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5389 | h5389
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5390 | h5390
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5391 | h5391
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5392 | h5392
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5393 | h5393
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5394 | h5394
                    · linarith only [h0, h1, h5387, h5389, h5394, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5396 | h5396
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5397 | h5397
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5398 | h5398
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5399 | h5399
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5400 | h5400
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5401 | h5401
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5402 | h5402
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5403 | h5403
                                    · linarith only [h0, h1, h5394, h5396, h5403, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                    · linarith only [h0, h1, h5394, h5396, h5400, h5403, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h0, h1, h5394, h5402, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h5394, h5401, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5408 | h5408
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5409 | h5409
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5410 | h5410
                                    · linarith only [h5396, h5400, h5410, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5412 | h5412
                                      · linarith only [h5396, h5400, h5408, h5412, hlam]
                                      · rcases h1bigk with h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c | h5414c
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h1, h5394, hc12, hc23, hlam, hphi, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h1, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h1, h5394, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h1, h5394, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h0, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5394, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h0, h1, h5394, h5396, h5408, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h0, h1, h5394, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5394, hc01, hc23, hlam, hphi, ht12, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5394, hc12, hc23, hlam, hphi, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          rcases p5414_3 (m.d 0 1) (by simp) with h5428 | h5428
                                          · linarith only [h1, h5428, hlam]
                                          · linarith only [h5385, h5428, hlam]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          rcases p5414_3 (m.d 0 1) (by simp) with h5431 | h5431
                                          · linarith only [h1, h5431, hlam]
                                          · linarith only [h5386, h5431, hlam]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5385, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5396, hlam, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5398, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5400, hlam, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5386, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5397, hlam, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h5399, hlam, p5414_0]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [h1, h5386, h5394, h5396, h5408, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5414_1]
                                        · have p5414_0 := h5414c.1
                                          have p5414_1 := h5414c.2.1
                                          have p5414_2 := h5414c.2.2.1
                                          have p5414_3 := h5414c.2.2.2
                                          linarith only [hlam, p5414_0]
                                  · linarith only [h0, h1, h5394, h5396, h5408, h5409, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h1, h5389, h5393, h5394, h5400, h5408, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h5396, h5399, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5396, h5398, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h5390, h5396, h5397, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5389, h5394, h5396, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5450 | h5450
                    · linarith only [h0, h1, h5387, h5450, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5452 | h5452
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5453 | h5453
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5454 | h5454
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5455 | h5455
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5456 | h5456
                              · linarith only [h5385, h5393, h5456, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5458 | h5458
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5459 | h5459
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5460 | h5460
                                    · linarith only [h0, h1, h5393, h5450, h5452, h5460, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5462 | h5462
                                      · linarith only [h5385, h5393, h5452, h5458, h5462, hlam]
                                      · rcases h1bigk with h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c | h5464c
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h1, h5450, h5453, h5458, h5460, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h1, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h1, h5450, h5452, h5458, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h1, h5450, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h0, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5450, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h0, h1, h5450, h5452, h5458, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h0, h1, h5450, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5450, hc01, hc23, hlam, hphi, ht12, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5450, hc12, hc23, hlam, hphi, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          rcases p5464_3 (m.d 0 1) (by simp) with h5478 | h5478
                                          · linarith only [h1, h5478, hlam]
                                          · linarith only [h5385, h5478, hlam]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          rcases p5464_3 (m.d 0 1) (by simp) with h5481 | h5481
                                          · linarith only [h1, h5481, hlam]
                                          · linarith only [h5386, h5481, hlam]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5385, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5452, hlam, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5454, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5456, hlam, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5386, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5453, hlam, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5455, hlam, p5464_0]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [h5386, h5452, h5458, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5464_1]
                                        · have p5464_0 := h5464c.1
                                          have p5464_1 := h5464c.2.1
                                          have p5464_2 := h5464c.2.2.1
                                          have p5464_3 := h5464c.2.2.2
                                          linarith only [hlam, p5464_0]
                                  · linarith only [h0, h1, h5450, h5459, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h5450, h5452, h5458, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h0, h1, h5452, h5455, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5452, h5454, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h5390, h5452, h5453, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h5389, h5450, h5452, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h5390, h5392, hlam]
              · linarith only [h1, h5385, h5391, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5502 | h5502
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5503 | h5503
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5504 | h5504
                  · linarith only [h5389, h5390, h5504, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5506 | h5506
                    · linarith only [h0, h1, h5387, h5506, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5508 | h5508
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5509 | h5509
                        · linarith only [h0, h5390, h5509, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5511 | h5511
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5512 | h5512
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5513 | h5513
                              · linarith only [h1, h5385, h5386, h5504, h5508, h5509, h5513, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5515 | h5515
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5516 | h5516
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5517 | h5517
                                    · linarith only [h1, h5386, h5504, h5506, h5508, h5509, h5517, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5519 | h5519
                                      · linarith only [h0, h5390, h5508, h5515, h5517, h5519, hlam]
                                      · rcases h1bigk with h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c | h5521c
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h1, h5506, h5508, h5515, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h1, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h1, h5506, h5508, h5515, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h1, h5506, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h0, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5506, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h0, h5390, h5508, h5515, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5509, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5506, hc01, hc23, hlam, hphi, ht12, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5506, hc12, hc23, hlam, hphi, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          rcases p5521_3 (m.d 0 1) (by simp) with h5535 | h5535
                                          · linarith only [h1, h5535, hlam]
                                          · linarith only [h5385, h5535, hlam]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5506, h5508, h5509, h5515, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5385, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5508, hlam, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5511, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5513, hlam, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5386, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5386, h5508, h5515, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h5512, hlam, p5521_0]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [h1, h5386, h5506, h5508, h5515, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5521_1]
                                        · have p5521_0 := h5521c.1
                                          have p5521_1 := h5521c.2.1
                                          have p5521_2 := h5521c.2.2.1
                                          have p5521_3 := h5521c.2.2.2
                                          linarith only [hlam, p5521_0]
                                  · linarith only [h0, h1, h5506, h5508, h5515, h5516, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                · linarith only [h0, h1, h5506, h5515, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5386, h5508, h5509, h5512, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1, h5386, h5508, h5509, h5511, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h5389, h5506, h5508, hc12, hc23, hlam, hphi]
                · linarith only [h1, h5386, h5503, hlam]
              · linarith only [h1, h5385, h5502, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5556 | h5556
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5557 | h5557
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5558 | h5558
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5559 | h5559
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5560 | h5560
                    · linarith only [h0, h1, h5387, h5560, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5562 | h5562
                      · linarith only [h0, h1, h5389, h5562, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5564 | h5564
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5565 | h5565
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5566 | h5566
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5567 | h5567
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5568 | h5568
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5569 | h5569
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5570 | h5570
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5571 | h5571
                                      · rcases h1bigk with h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c | h5572c
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h1, h5560, h5564, h5569, h5571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h1, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h1, h5560, h5562, h5564, h5569, h5571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h1, h5560, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h0, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5560, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5562, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h0, h1, h5560, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5560, hc01, hc23, hlam, hphi, ht12, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5560, hc12, hc23, hlam, hphi, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5560, h5562, h5564, h5569, h5571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          rcases p5572_3 (m.d 0 1) (by simp) with h5587 | h5587
                                          · linarith only [h1, h5587, hlam]
                                          · linarith only [h5386, h5587, hlam]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5385, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5564, h5569, h5571, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5565, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h1, h5385, h5560, h5564, h5569, h5571, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5386, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5564, hlam, p5572_1]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5566, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [h5567, hlam, p5572_0]
                                        · have p5572_0 := h5572c.1
                                          have p5572_1 := h5572c.2.1
                                          have p5572_2 := h5572c.2.2.1
                                          have p5572_3 := h5572c.2.2.2
                                          linarith only [hlam, p5572_0]
                                      · linarith only [h1, h5385, h5560, h5567, h5571, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h5386, h5389, h5567, h5570, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h5560, h5564, h5569, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h1, h5560, h5564, h5568, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h5385, h5559, h5562, h5564, h5567, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1, h5385, h5562, h5564, h5566, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h5385, h5562, h5564, h5565, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h5385, h5389, h5556, h5560, h5564, hc12, hc23, hlam, hphi]
                  · linarith only [h5389, h5556, h5559, hlam]
                · linarith only [h1, h5385, h5389, h5556, h5558, hlam]
              · linarith only [h1, h5385, h5557, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5611 | h5611
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5612 | h5612
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5613 | h5613
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5614 | h5614
                    · linarith only [h0, h1, h5387, h5614, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5616 | h5616
                      · linarith only [h0, h5389, h5616, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5618 | h5618
                        · linarith only [h0, h5556, h5618, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5620 | h5620
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5621 | h5621
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5622 | h5622
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5623 | h5623
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5624 | h5624
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5625 | h5625
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5626 | h5626
                                      · rcases h1bigk with h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, h5614, hc12, hc23, hlam, hphi, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, h5614, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, h5614, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h0, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5614, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5616, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5618, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5614, hc01, hc23, hlam, hphi, ht12, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5614, hc12, hc23, hlam, hphi, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5614, h5620, h5626, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5614, h5618, hc12, hc23, hlam, hphi, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5385, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5385, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5620, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, h5385, h5614, h5618, hc12, hc23, hlam, hphi, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5386, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h1, h5386, h5614, hc12, hc23, hlam, hphi, p5627_1]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5621, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [h5622, hlam, p5627_0]
                                        · have p5627_0 := h5627c.1
                                          have p5627_1 := h5627c.2.1
                                          have p5627_2 := h5627c.2.2.1
                                          have p5627_3 := h5627c.2.2.2
                                          linarith only [hlam, p5627_0]
                                      · linarith only [h1, h5385, h5614, h5622, h5626, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h1, h5385, h5614, h5622, h5625, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · linarith only [h1, h5385, h5614, h5622, h5624, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h1, h5385, h5614, h5622, h5623, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h5385, h5613, h5614, h5616, h5622, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h5621, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5385, h5616, h5620, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5660 | h5660
                    · linarith only [h0, h5387, h5660, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5662 | h5662
                      · linarith only [h0, h5389, h5662, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5664 | h5664
                        · linarith only [h0, h5556, h5664, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5666 | h5666
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5667 | h5667
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5668 | h5668
                              · linarith only [h1, h5385, h5613, h5668, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5670 | h5670
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5671 | h5671
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5672 | h5672
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5673 | h5673
                                      · linarith only [h5385, h5613, h5666, h5673, hlam]
                                      · rcases h1bigk with h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c | h5675c
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, h5660, hc12, hc23, hlam, hphi, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, h5660, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, h5660, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h0, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5660, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5662, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5664, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5660, hc01, hc23, hlam, hphi, ht12, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5660, hc12, hc23, hlam, hphi, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5660, h5662, hc12, hc23, hlam, hphi, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5660, h5664, hc12, hc23, hlam, hphi, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5385, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5385, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5666, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5668, hlam, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5386, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, h5386, h5660, hc12, hc23, hlam, hphi, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h5667, hlam, p5675_0]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [h1, h5386, h5660, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5675_1]
                                        · have p5675_0 := h5675c.1
                                          have p5675_1 := h5675c.2.1
                                          have p5675_2 := h5675c.2.2.1
                                          have p5675_3 := h5675c.2.2.2
                                          linarith only [hlam, p5675_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5701 | h5701
                                      · linarith only [h0, h5389, h5672, h5701, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c | h5703c
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, h5660, hc12, hc23, hlam, hphi, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, h5660, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, h5660, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h0, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5660, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5662, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5664, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5660, hc01, hc23, hlam, hphi, ht12, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5660, hc12, hc23, hlam, hphi, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5660, h5662, hc12, hc23, hlam, hphi, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5660, h5664, hc12, hc23, hlam, hphi, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5385, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5385, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5666, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5668, hlam, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5386, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, h5386, h5660, hc12, hc23, hlam, hphi, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h5667, hlam, p5703_0]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [h1, h5386, h5660, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5703_1]
                                        · have p5703_0 := h5703c.1
                                          have p5703_1 := h5703c.2.1
                                          have p5703_2 := h5703c.2.2.1
                                          have p5703_3 := h5703c.2.2.2
                                          linarith only [hlam, p5703_0]
                                  · linarith only [h0, h1, h5660, h5671, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h5660, h5670, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5385, h5662, h5667, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5385, h5662, h5666, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h5386, h5612, hlam]
              · linarith only [h1, h5385, h5611, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5735 | h5735
        · linarith only [h0, h1, h5735, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5737 | h5737
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5738 | h5738
            · linarith only [h0, h5386, h5738, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5740 | h5740
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5741 | h5741
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5742 | h5742
                  · linarith only [h0, h5386, h5737, h5742, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5744 | h5744
                    · linarith only [h0, h1, h5735, h5744, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5746 | h5746
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5747 | h5747
                        · linarith only [h0, h5386, h5738, h5747, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5749 | h5749
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5750 | h5750
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5751 | h5751
                              · linarith only [h0, h5385, h5386, h5737, h5742, h5751, hlam]
                              · linarith only [h0, h5386, h5746, h5751, hc24, hc45, hlam, hphi]
                            · linarith only [h0, h1, h5741, h5746, h5750, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h5746, h5749, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5735, h5737, h5746, hc12, hc23, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5757 | h5757
                  · linarith only [h0, h1, h5737, h5741, h5757, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5759 | h5759
                    · linarith only [h0, h1, h5735, h5759, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5761 | h5761
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5762 | h5762
                        · linarith only [h0, h5738, h5762, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5764 | h5764
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5765 | h5765
                            · linarith only [h0, h1, h5741, h5759, h5761, h5765, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1, h5761, h5765, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1, h5761, h5764, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h5735, h5737, h5761, hc12, hc23, hlam, hphi]
              · linarith only [h0, h1, h5737, h5740, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5771 | h5771
            · linarith only [h5385, h5386, h5737, h5771, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5773 | h5773
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5774 | h5774
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5775 | h5775
                  · linarith only [h5385, h5386, h5775, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5777 | h5777
                    · linarith only [h0, h5735, h5777, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5779 | h5779
                      · linarith only [h0, h5737, h5779, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5781 | h5781
                        · linarith only [h0, h5386, h5771, h5781, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5783 | h5783
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5784 | h5784
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5785 | h5785
                              · linarith only [h5385, h5386, h5737, h5775, h5784, h5785, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5787 | h5787
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5788 | h5788
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5789 | h5789
                                    · linarith only [h0, h5386, h5785, h5787, h5789, hc12, hc23, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5791 | h5791
                                      · linarith only [h5385, h5386, h5783, h5789, h5791, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                      · rcases h1bigk with h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5386, h5781, h5789, hc12, hc45, hlam, hphi, ht23, ht34, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h1, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5386, h5781, h5789, hc14, hc45, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5386, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h0, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5777, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5779, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5781, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hc01, hc13, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5777, hc12, hc23, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5777, h5779, hc12, hc23, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5385, h5386, h5777, h5779, hc12, hc23, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5385, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5385, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5783, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5785, hlam, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hc01, hc15, hlam, hphi, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5781, h5789, hc12, hc45, hlam, hphi, ht23, ht34, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5784, hlam, p5793_0]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [h5779, h5781, h5789, hc12, hc45, hlam, hphi, ht23, ht34, p5793_1]
                                        · have p5793_0 := h5793c.1
                                          have p5793_1 := h5793c.2.1
                                          have p5793_2 := h5793c.2.2.1
                                          have p5793_3 := h5793c.2.2.2
                                          linarith only [hlam, p5793_0]
                                  · linarith only [h1, h5774, h5777, h5788, hlam]
                                · linarith only [h1, h5385, h5777, h5779, h5787, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h1, h5774, h5784, hlam]
                          · linarith only [h1, h5385, h5779, h5783, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5823 | h5823
                  · linarith only [h5385, h5386, h5823, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5825 | h5825
                    · linarith only [h0, h1, h5774, h5825, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5827 | h5827
                      · linarith only [h0, h5737, h5827, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5829 | h5829
                        · linarith only [h0, h1, h5771, h5774, h5829, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5831 | h5831
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5832 | h5832
                            · linarith only [h0, h1, h5774, h5825, h5832, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h5385, h5827, h5832, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5385, h5827, h5831, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h5385, h5773, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h5837 | h5837
      · rcases m.htr 0 2 3 (by decide) (by decide) with h5838 | h5838
        · linarith only [h0, h1, h5838, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5840 | h5840
          · linarith only [h0, h5385, h5840, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5842 | h5842
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5843 | h5843
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5844 | h5844
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5845 | h5845
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5846 | h5846
                    · linarith only [h0, h1, h5838, h5846, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5848 | h5848
                      · linarith only [h0, h5385, h5840, h5848, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5850 | h5850
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5851 | h5851
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5852 | h5852
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5853 | h5853
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5854 | h5854
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5855 | h5855
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5856 | h5856
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5857 | h5857
                                      · rcases h1bigk with h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5385, h5846, h5850, h5851, h5855, h5857, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h1, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5385, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5385, h5846, h5851, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h0, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5846, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5848, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h0, h5385, h5846, h5851, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5846, hc01, hc23, hlam, hphi, ht12, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5846, hc12, hc23, hlam, hphi, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h0, h5385, h5846, hc12, hc23, hlam, hphi, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          rcases p5858_3 (m.d 0 1) (by simp) with h5873 | h5873
                                          · linarith only [h1, h5873, hlam]
                                          · linarith only [h5837, h5873, hlam]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h0, h5850, h5855, h5857, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5848, h5850, h5855, h5857, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5851, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          rcases p5858_3 (m.d 0 1) (by simp) with h5880 | h5880
                                          · linarith only [h5385, h5880, hlam]
                                          · linarith only [h5837, h5880, hlam]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5837, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5850, hlam, p5858_1]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5852, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [h5853, hlam, p5858_0]
                                        · have p5858_0 := h5858c.1
                                          have p5858_1 := h5858c.2.1
                                          have p5858_2 := h5858c.2.2.1
                                          have p5858_3 := h5858c.2.2.2
                                          linarith only [hlam, p5858_0]
                                      · linarith only [h0, h5385, h5846, h5850, h5851, h5856, h5857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                    · linarith only [h5385, h5837, h5840, h5851, h5853, h5856, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h5385, h5846, h5850, h5851, h5855, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                · linarith only [h0, h5385, h5846, h5850, h5851, h5854, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h0, h5385, h5850, h5853, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                            · linarith only [h0, h5385, h5850, h5851, h5852, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h1, h5843, h5850, h5851, hc03, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h5385, h5842, h5848, h5850, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h5385, h5842, h5845, hlam]
                · linarith only [h0, h1, h5842, h5844, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5898 | h5898
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5899 | h5899
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5900 | h5900
                    · linarith only [h0, h1, h5838, h5900, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5902 | h5902
                      · linarith only [h0, h5840, h5902, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5904 | h5904
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5905 | h5905
                          · linarith only [h0, h1, h5843, h5900, h5905, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h5904, h5905, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h0, h5385, h5842, h5902, h5904, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h5842, h5843, h5899, hlam]
                · linarith only [h0, h1, h5842, h5898, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h5911 | h5911
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5912 | h5912
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5913 | h5913
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5914 | h5914
                    · linarith only [h0, h1, h5838, h5914, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5916 | h5916
                      · linarith only [h0, h5840, h5916, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5918 | h5918
                        · linarith only [h0, h5842, h5918, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5920 | h5920
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h5921 | h5921
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h5922 | h5922
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h5923 | h5923
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h5924 | h5924
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5925 | h5925
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5926 | h5926
                                      · rcases h1bigk with h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c | h5927c
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5385, h5914, h5920, hc12, hc23, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h1, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5385, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5385, h5914, h5920, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h0, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5914, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5916, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5918, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5914, hc01, hc23, hlam, hphi, ht12, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5914, hc12, hc23, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h0, h5385, h5914, hc12, hc23, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5914, h5918, hc12, hc23, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5837, h5918, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5916, hc12, hc24, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5920, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5914, h5918, h5920, hc12, hc23, hlam, hphi, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5837, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5837, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5927_1]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5921, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [h5922, hlam, p5927_0]
                                        · have p5927_0 := h5927c.1
                                          have p5927_1 := h5927c.2.1
                                          have p5927_2 := h5927c.2.2.1
                                          have p5927_3 := h5927c.2.2.2
                                          linarith only [hlam, p5927_0]
                                      · rcases h1bigk with h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c | h5953c
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5385, h5914, h5920, hc12, hc23, hlam, hphi, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h1, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5385, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5385, h5914, h5920, h5922, h5926, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h0, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5914, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5916, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5918, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5914, hc01, hc23, hlam, hphi, ht12, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5914, hc12, hc23, hlam, hphi, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5385, h5837, h5914, h5922, h5926, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5914, h5922, h5926, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5837, h5922, h5926, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5916, h5923, hc12, hc23, hlam, hphi, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5920, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5916, h5922, h5923, h5926, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5837, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5837, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5953_1]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5921, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [h5922, hlam, p5953_0]
                                        · have p5953_0 := h5953c.1
                                          have p5953_1 := h5953c.2.1
                                          have p5953_2 := h5953c.2.2.1
                                          have p5953_3 := h5953c.2.2.2
                                          linarith only [hlam, p5953_0]
                                    · linarith only [h5385, h5837, h5916, h5922, h5925, hlam]
                                  · linarith only [h0, h5385, h5916, h5923, h5924, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h5385, h5837, h5914, h5918, h5920, h5923, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h5385, h5837, h5918, h5922, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h5385, h5837, h5918, h5920, h5921, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h5911, h5920, hlam]
                  · linarith only [h5385, h5837, h5913, hlam]
                · linarith only [h1, h5837, h5912, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h5987 | h5987
                · rcases m.htr 0 4 5 (by decide) (by decide) with h5988 | h5988
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h5989 | h5989
                    · linarith only [h0, h1, h5911, h5989, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h5991 | h5991
                      · linarith only [h0, h5840, h5991, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h5993 | h5993
                        · linarith only [h0, h5842, h5993, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h5995 | h5995
                          · linarith only [h1, h5837, h5911, h5989, h5993, h5995, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h5837, h5993, h5995, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h5837, h5911, h5988, hlam]
                · linarith only [h1, h5837, h5987, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6000 | h6000
        · linarith only [h0, h1, h6000, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6002 | h6002
          · linarith only [h0, h5385, h6002, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6004 | h6004
            · linarith only [h0, h5837, h6004, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6006 | h6006
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6007 | h6007
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6008 | h6008
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6009 | h6009
                    · linarith only [h0, h1, h6000, h6009, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6011 | h6011
                      · linarith only [h0, h5837, h6002, h6008, h6011, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6013 | h6013
                        · linarith only [h0, h5837, h6004, h6013, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6015 | h6015
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6016 | h6016
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h6017 | h6017
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h6018 | h6018
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h6019 | h6019
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6020 | h6020
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6021 | h6021
                                      · rcases h1bigk with h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c | h6022c
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h5837, h6009, h6015, h6017, hc12, hc23, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h1, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h5385, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h5837, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6009, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6011, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6013, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6009, hc01, hc23, hlam, hphi, ht12, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6009, hc12, hc23, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, h5385, h6009, hc12, hc23, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, h5837, h6009, hc12, hc23, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6011, hc12, hc24, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6015, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, h5837, h6009, h6015, hc12, hc23, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6013, hc12, hc25, hlam, hphi, p6022_1]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6016, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [h6017, hlam, p6022_0]
                                        · have p6022_0 := h6022c.1
                                          have p6022_1 := h6022c.2.1
                                          have p6022_2 := h6022c.2.2.1
                                          have p6022_3 := h6022c.2.2.2
                                          linarith only [hlam, p6022_0]
                                      · rcases h1bigk with h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c | h6048c
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h1, h6009, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h1, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h5385, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h5837, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h0, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6009, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6011, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6013, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6009, hc01, hc23, hlam, hphi, ht12, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6009, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h5385, h6008, h6009, h6021, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h0, h5837, h6009, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6011, h6018, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6015, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h0, h5837, h6011, h6018, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6013, h6018, h6020, hc12, hc23, hlam, hphi, p6048_1]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6016, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [h6017, hlam, p6048_0]
                                        · have p6048_0 := h6048c.1
                                          have p6048_1 := h6048c.2.1
                                          have p6048_2 := h6048c.2.2.1
                                          have p6048_3 := h6048c.2.2.2
                                          linarith only [hlam, p6048_0]
                                    · linarith only [h0, h5385, h6006, h6008, h6011, h6020, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1, h6009, h6019, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h0, h1, h6009, h6018, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h0, h5385, h6006, h6008, h6017, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h1, h6016, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h6006, h6015, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6080 | h6080
                    · linarith only [h0, h5385, h6008, h6080, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6082 | h6082
                      · linarith only [h0, h5385, h6008, h6082, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6084 | h6084
                        · linarith only [h0, h6004, h6084, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6086 | h6086
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6087 | h6087
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h6088 | h6088
                              · linarith only [h0, h5385, h6008, h6080, h6086, h6088, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h5385, h6088, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h1, h6007, h6087, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h1, h6086, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6093 | h6093
                  · linarith only [h6006, h6007, h6093, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6095 | h6095
                    · linarith only [h0, h1, h6007, h6095, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6097 | h6097
                      · linarith only [h0, h5385, h6093, h6097, hc24, hc45, hlam, hphi]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6099 | h6099
                        · linarith only [h0, h6004, h6099, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6101 | h6101
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h6102 | h6102
                            · linarith only [h0, h5385, h6006, h6007, h6095, h6102, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h6102, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h6006, h6101, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h6106 | h6106
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6107 | h6107
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6108 | h6108
                    · linarith only [h0, h6000, h6108, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6110 | h6110
                      · linarith only [h0, h6002, h6110, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6112 | h6112
                        · linarith only [h0, h6004, h6112, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6114 | h6114
                          · linarith only [h0, h5837, h6006, h6106, h6108, h6114, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6114, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h6006, h6106, h6107, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h6118 | h6118
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6119 | h6119
                    · linarith only [h0, h1, h6106, h6119, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6121 | h6121
                      · linarith only [h0, h6002, h6121, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6123 | h6123
                        · linarith only [h0, h6004, h6123, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6125 | h6125
                          · linarith only [h0, h1, h6006, h6119, h6125, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6125, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h6128 | h6128
                    · linarith only [h0, h1, h6006, h6118, h6128, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h6130 | h6130
                      · linarith only [h0, h1, h6002, h6006, h6130, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h6132 | h6132
                        · linarith only [h0, h1, h6004, h6006, h6118, h6132, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h6134 | h6134
                          · linarith only [h0, h1, h6006, h6128, h6134, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h6134, hc12, hc34, hlam, hphi, ht23]

end R2N4
