import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S8
import Jsp000404.R1LeavesN7_5S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4901 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h4903 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h5375 | h5375
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5376 | h5376
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5377 | h5377
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5378 | h5378
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5379 | h5379
          · linarith only [h0, h4901, h5379, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5381 | h5381
            · linarith only [h0, h4903, h5381, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5383 | h5383
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5384 | h5384
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5385 | h5385
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5386 | h5386
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5387 | h5387
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5388 | h5388
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5389 | h5389
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5390 | h5390
                            · rcases h0bigk with h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c | h5391c
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h1, h5379, hc02, hc23, hlam, hphi, p5391_1]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h1, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h0, h1, h4903, h5379, hc12, hc23, hlam, hphi, p5391_1]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                rcases p5391_3 (m.d 0 1) (by simp) with h5396 | h5396
                                · rcases p5391_3 (m.d 0 2) (by simp) with h5397 | h5397
                                  · linarith only [h0, h5397, hlam]
                                  · linarith only [h5375, h5397, hlam]
                                · linarith only [h4900, h5396, hlam]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h0, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h4901, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h4903, hlam, p5391_1]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                rcases p5391_3 (m.d 0 1) (by simp) with h5405 | h5405
                                · rcases p5391_3 (m.d 0 2) (by simp) with h5406 | h5406
                                  · rcases p5391_3 (m.d 0 3) (by simp) with h5407 | h5407
                                    · rcases p5391_3 (m.d 0 4) (by simp) with h5408 | h5408
                                      · rcases p5391_3 (m.d 0 5) (by simp) with h5409 | h5409
                                        · linarith only [h5375, h5409, hlam]
                                        · rcases h0emin with h5411 | h5411 | h5411 | h5411 | h5411
                                          · rcases h1bigk with h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c | h5412c
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h1, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h1, h5379, h5381, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              rcases p5412_3 (m.d 0 1) (by simp) with h5417 | h5417
                                              · rcases p5412_3 (m.d 1 2) (by simp) with h5418 | h5418
                                                · linarith only [h0, h5418, hlam]
                                                · linarith only [h5383, h5418, hlam]
                                              · linarith only [h5417, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h0, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5379, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5381, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h0, h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5379, h5411, hc23, hlam, ht01, ht12, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              rcases p5412_3 (m.d 0 1) (by simp) with h5428 | h5428
                                              · linarith only [h1, h5428, hlam]
                                              · linarith only [h0, h5428, hlam]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              rcases p5412_3 (m.d 0 1) (by simp) with h5432 | h5432
                                              · linarith only [h1, h5432, hlam]
                                              · linarith only [h4899, h5432, hlam]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p5391_1, p5412_2]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h4899, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h4899, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5412_1, u0elo0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5384, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h1, h4899, h5379, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h4900, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5383, hlam, p5412_1]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5385, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [h5386, hlam, p5412_0]
                                            · have p5412_0 := h5412c.1
                                              have p5412_1 := h5412c.2.1
                                              have p5412_2 := h5412c.2.2.1
                                              have p5412_3 := h5412c.2.2.2
                                              linarith only [hlam, p5412_0]
                                          · rcases h1bigk with h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c | h5446c
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h1, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h1, h5379, h5381, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              rcases p5446_3 (m.d 0 1) (by simp) with h5451 | h5451
                                              · rcases p5446_3 (m.d 1 2) (by simp) with h5452 | h5452
                                                · linarith only [h0, h5452, hlam]
                                                · linarith only [h5383, h5452, hlam]
                                              · linarith only [h5451, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h0, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5379, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5381, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h0, h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h4899, h4903, h5379, h5411, hc23, hlam, ht01, ht12, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              rcases p5446_3 (m.d 0 1) (by simp) with h5462 | h5462
                                              · linarith only [h1, h5462, hlam]
                                              · linarith only [h0, h5462, hlam]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              rcases p5446_3 (m.d 0 1) (by simp) with h5466 | h5466
                                              · linarith only [h1, h5466, hlam]
                                              · linarith only [h4899, h5466, hlam]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p5391_1, p5446_2]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h4899, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h1, h4899, h5379, hc12, hc23, hlam, hphi, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5384, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h1, h4899, h5379, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h4900, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5383, hlam, p5446_1]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5385, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [h5386, hlam, p5446_0]
                                            · have p5446_0 := h5446c.1
                                              have p5446_1 := h5446c.2.1
                                              have p5446_2 := h5446c.2.2.1
                                              have p5446_3 := h5446c.2.2.2
                                              linarith only [hlam, p5446_0]
                                          · rcases h1bigk with h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c | h5480c
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h1, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h1, h5379, h5381, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              rcases p5480_3 (m.d 0 1) (by simp) with h5485 | h5485
                                              · rcases p5480_3 (m.d 1 2) (by simp) with h5486 | h5486
                                                · linarith only [h0, h5486, hlam]
                                                · linarith only [h5383, h5486, hlam]
                                              · linarith only [h5485, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h0, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5379, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5381, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h0, h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h4899, h4903, h5379, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5391_1, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              rcases p5480_3 (m.d 0 1) (by simp) with h5496 | h5496
                                              · linarith only [h1, h5496, hlam]
                                              · linarith only [h0, h5496, hlam]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              rcases p5480_3 (m.d 0 1) (by simp) with h5500 | h5500
                                              · linarith only [h1, h5500, hlam]
                                              · linarith only [h4899, h5500, hlam]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p5391_1, p5480_2]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h4899, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h1, h4899, h5379, hc12, hc23, hlam, hphi, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5384, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h1, h4899, h5379, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h4900, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5383, hlam, p5480_1]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5385, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [h5386, hlam, p5480_0]
                                            · have p5480_0 := h5480c.1
                                              have p5480_1 := h5480c.2.1
                                              have p5480_2 := h5480c.2.2.1
                                              have p5480_3 := h5480c.2.2.2
                                              linarith only [hlam, p5480_0]
                                          · rcases h1bigk with h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c | h5514c
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h1, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h1, h5379, h5381, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              rcases p5514_3 (m.d 0 1) (by simp) with h5519 | h5519
                                              · rcases p5514_3 (m.d 1 2) (by simp) with h5520 | h5520
                                                · linarith only [h0, h5520, hlam]
                                                · linarith only [h5383, h5520, hlam]
                                              · linarith only [h5519, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h0, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5379, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5381, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h0, h1, h5379, h5383, h5388, h5390, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h4899, h5379, h5411, hc23, hlam, ht01, ht12, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              rcases p5514_3 (m.d 0 1) (by simp) with h5530 | h5530
                                              · linarith only [h1, h5530, hlam]
                                              · linarith only [h0, h5530, hlam]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              rcases p5514_3 (m.d 0 1) (by simp) with h5534 | h5534
                                              · linarith only [h1, h5534, hlam]
                                              · linarith only [h4899, h5534, hlam]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h0, h1, h4900, hlam, p5391_1, p5514_2]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h4899, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h1, h4899, h5379, hc12, hc23, hlam, hphi, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5384, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h1, h4899, h5379, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h4900, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5383, hlam, p5514_1]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5385, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [h5386, hlam, p5514_0]
                                            · have p5514_0 := h5514c.1
                                              have p5514_1 := h5514c.2.1
                                              have p5514_2 := h5514c.2.2.1
                                              have p5514_3 := h5514c.2.2.2
                                              linarith only [hlam, p5514_0]
                                          · linarith only [h1, h4899, h4903, h5379, h5411, hc23, hlam, ht01, ht12, p5391_1]
                                      · linarith only [h5378, h5408, hlam]
                                    · linarith only [h5377, h5407, hlam]
                                  · linarith only [h5375, h5406, hlam]
                                · linarith only [h4900, h5405, hlam]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h4899, hc14, hlam, hphi, ht0b, ht45, ht5b, p5391_1, u0elo2]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h0, h5383, h5388, h5390, hc45, hlam, hphi, ht0b, ht5b, p5391_1, u0elo2]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h0, h4903, h5383, h5388, h5390, hc45, hlam, hphi, ht0b, ht5b, p5391_1, u0elo2]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                rcases p5391_3 (m.d 0 1) (by simp) with h5557 | h5557
                                · linarith only [h1, h5557, hlam]
                                · linarith only [h4900, h5557, hlam]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h4899, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h0, h5383, h5388, h5390, hc45, hlam, hphi, ht0b, ht5b, p5391_1, u0elo3]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h5376, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                rcases p5391_3 (m.d 0 1) (by simp) with h5564 | h5564
                                · rcases p5391_3 (m.d 0 2) (by simp) with h5565 | h5565
                                  · linarith only [h4903, h5565, hlam]
                                  · linarith only [h5375, h5565, hlam]
                                · linarith only [h4900, h5564, hlam]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h4900, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h5375, hlam, p5391_1]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h5377, hlam, p5391_0]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [h5378, hlam, p5391_1]
                              · have p5391_0 := h5391c.1
                                have p5391_1 := h5391c.2.1
                                have p5391_2 := h5391c.2.2.1
                                have p5391_3 := h5391c.2.2.2
                                linarith only [hlam, p5391_0]
                            · linarith only [h1, h4899, h5379, h5386, h5390, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h4899, h5379, h5386, h5389, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1, h4899, h5379, h5381, h5388, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h4899, h5379, h5386, h5387, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h4899, h5378, h5381, h5383, h5386, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · linarith only [h0, h1, h5383, h5385, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1, h4899, h5381, h5383, h5384, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h4903, h5375, h5383, hc12, hc24, hlam, hphi]
        · linarith only [h4903, h5375, h5378, hlam]
      · linarith only [h1, h4899, h4903, h5375, h5377, hlam]
    · linarith only [h1, h4899, h5376, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5585 | h5585
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5586 | h5586
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5587 | h5587
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5588 | h5588
          · linarith only [h0, h4901, h5588, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5590 | h5590
            · linarith only [h0, h1, h4903, h5587, h5588, h5590, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5592 | h5592
              · linarith only [h0, h5375, h5592, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5594 | h5594
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5595 | h5595
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5596 | h5596
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5597 | h5597
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5598 | h5598
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5599 | h5599
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5600 | h5600
                            · rcases h0bigk with h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h1, h5588, hc02, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h1, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, h1, h5375, h5587, h5588, hc12, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, h1, h5375, h5588, hc12, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4901, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4903, hlam, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h5375, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4899, hc14, hlam, hphi, ht0b, ht45, ht5b, p5601_1, u0elo2]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                rcases p5601_3 (m.d 0 1) (by simp) with h5613 | h5613
                                · linarith only [h1, h5613, hlam]
                                · linarith only [h0, h5613, hlam]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4899, h5594, h5600, hc45, hlam, hphi, ht0b, ht5b, p5601_1, u0elo2]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                rcases p5601_3 (m.d 0 1) (by simp) with h5618 | h5618
                                · linarith only [h1, h5618, hlam]
                                · linarith only [h4900, h5618, hlam]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4899, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, h1, h4899, h5588, hc12, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h5585, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, h1, h4899, h5375, h5588, hc12, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h4900, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h0, h1, h4900, h5588, hc12, hc23, hlam, hphi, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h5586, hlam, p5601_0]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [h5587, hlam, p5601_1]
                              · have p5601_0 := h5601c.1
                                have p5601_1 := h5601c.2.1
                                have p5601_2 := h5601c.2.2.1
                                have p5601_3 := h5601c.2.2.2
                                linarith only [hlam, p5601_0]
                            · linarith only [h1, h4899, h5588, h5596, h5600, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h4899, h4903, h5588, h5596, h5599, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1, h4900, h5588, h5595, h5598, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h1, h4899, h5588, h5596, h5597, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h4899, h5587, h5588, h5590, h5596, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h5595, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h4899, h5590, h5594, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5638 | h5638
          · linarith only [h0, h4901, h5638, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5640 | h5640
            · linarith only [h0, h4903, h5640, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5642 | h5642
              · linarith only [h0, h5375, h5642, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5644 | h5644
                · rcases m.htr 1 3 5 (by decide) (by decide) with h5645 | h5645
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h5646 | h5646
                    · linarith only [h4899, h5587, h5646, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h5648 | h5648
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h5649 | h5649
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h5650 | h5650
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5651 | h5651
                            · linarith only [h4899, h5587, h5644, h5651, hlam]
                            · rcases h0bigk with h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h1, h5638, hc02, hc23, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h1, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, h1, h4903, h5638, hc12, hc23, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, h1, h5375, h5638, hc12, hc23, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h4901, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h4903, hlam, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h5375, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5653_1, u0elo2]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                rcases p5653_3 (m.d 0 1) (by simp) with h5665 | h5665
                                · linarith only [h1, h5665, hlam]
                                · linarith only [h0, h5665, hlam]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                rcases p5653_3 (m.d 0 1) (by simp) with h5669 | h5669
                                · linarith only [h1, h5669, hlam]
                                · linarith only [h4899, h5669, hlam]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                rcases p5653_3 (m.d 0 1) (by simp) with h5672 | h5672
                                · linarith only [h1, h5672, hlam]
                                · linarith only [h4900, h5672, hlam]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h4899, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, h5587, h5650, hc12, hc24, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h5585, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h5587, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h4900, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h0, h5587, h5650, hc12, hc24, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h5586, hlam, p5653_0]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [h4899, h5587, h5640, h5650, hc12, hc24, hlam, hphi, p5653_1]
                              · have p5653_0 := h5653c.1
                                have p5653_1 := h5653c.2.1
                                have p5653_2 := h5653c.2.2.1
                                have p5653_3 := h5653c.2.2.2
                                linarith only [hlam, p5653_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h5685 | h5685
                            · linarith only [h1, h4899, h5638, h5644, h5650, h5685, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases h0bigk with h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c | h5687c
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h1, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h4903, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h5375, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h4901, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h4903, hlam, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h5375, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5687_1, u0elo2]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                rcases p5687_3 (m.d 0 1) (by simp) with h5699 | h5699
                                · linarith only [h1, h5699, hlam]
                                · linarith only [h0, h5699, hlam]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                rcases p5687_3 (m.d 0 1) (by simp) with h5703 | h5703
                                · linarith only [h1, h5703, hlam]
                                · linarith only [h4899, h5703, hlam]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                rcases p5687_3 (m.d 0 1) (by simp) with h5706 | h5706
                                · linarith only [h1, h5706, hlam]
                                · linarith only [h4900, h5706, hlam]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h4899, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h4899, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h5585, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h5587, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h4900, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h4900, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h5586, hlam, p5687_0]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [h0, h1, h4900, h4903, h5638, hc12, hc23, hlam, hphi, p5687_1]
                              · have p5687_0 := h5687c.1
                                have p5687_1 := h5687c.2.1
                                have p5687_2 := h5687c.2.2.1
                                have p5687_3 := h5687c.2.2.2
                                linarith only [hlam, p5687_0]
                        · linarith only [h1, h4900, h5638, h5645, h5649, hlam]
                      · linarith only [h1, h4899, h4900, h5638, h5644, h5648, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h1, h4899, h5640, h5645, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h4899, h5640, h5644, hc12, hc34, hlam, hphi, ht23]
      · linarith only [h1, h4900, h5586, hlam]
    · linarith only [h1, h4899, h5585, hlam]

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4901 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h4903 | h4903
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1_x0 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900 h4901 h4903
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1_x1 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900 h4901 h4903

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h4901 | h4901
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900 h4901
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900 h4901

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h5725 | h5725
  · linarith only [h0, h1, h5725, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h5727 | h5727
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5728 | h5728
      · linarith only [h0, h4900, h5728, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5730 | h5730
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5731 | h5731
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5732 | h5732
            · linarith only [h0, h4900, h5727, h5732, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5734 | h5734
              · linarith only [h0, h5725, h5734, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5736 | h5736
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5737 | h5737
                  · linarith only [h0, h4900, h5728, h5737, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5739 | h5739
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5740 | h5740
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5741 | h5741
                        · linarith only [h4899, h4900, h5732, h5734, h5740, h5741, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h4900, h5736, h5741, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h1, h5731, h5736, h5740, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h0, h1, h5736, h5739, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h5725, h5727, h5736, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5747 | h5747
            · linarith only [h1, h4899, h5731, h5747, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5749 | h5749
              · linarith only [h0, h5725, h5749, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5751 | h5751
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5752 | h5752
                  · linarith only [h0, h5728, h5752, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5754 | h5754
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5755 | h5755
                      · linarith only [h0, h1, h5731, h5749, h5751, h5755, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1, h5751, h5755, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h5751, h5754, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h5725, h5727, h5751, hc12, hc23, hlam, hphi]
        · linarith only [h0, h1, h5727, h5730, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h5761 | h5761
      · linarith only [h4899, h4900, h5727, h5761, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h5763 | h5763
        · rcases m.htr 0 3 5 (by decide) (by decide) with h5764 | h5764
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5765 | h5765
            · linarith only [h4899, h4900, h5765, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5767 | h5767
              · linarith only [h0, h5725, h5767, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5769 | h5769
                · linarith only [h0, h5727, h5769, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5771 | h5771
                  · linarith only [h0, h4900, h5761, h5771, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5773 | h5773
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5774 | h5774
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5775 | h5775
                        · linarith only [h4899, h5727, h5765, h5775, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5777 | h5777
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5778 | h5778
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5779 | h5779
                              · linarith only [h0, h4900, h5775, h5779, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5781 | h5781
                                · linarith only [h4899, h4900, h5771, h5773, h5779, h5781, hlam]
                                · rcases h0bigk with h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c | h5783c
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h0, h4900, h5771, hc12, hc25, hlam, hphi, p5783_1]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h1, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h0, h4900, h5727, h5771, h5779, hc12, hc45, hlam, hphi, ht23, ht34, p5783_1]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h4900, hlam, p5783_1]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h0, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5725, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5727, hlam, p5783_1]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5761, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h4899, hc14, hlam, hphi, ht0b, ht45, ht5b, p5783_1, u0elo2]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    rcases p5783_3 (m.d 0 1) (by simp) with h5795 | h5795
                                    · linarith only [h1, h5795, hlam]
                                    · linarith only [h0, h5795, hlam]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    rcases p5783_3 (m.d 0 1) (by simp) with h5799 | h5799
                                    · linarith only [h1, h5799, hlam]
                                    · linarith only [h4899, h5799, hlam]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h4899, h4900, h5769, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5783_1, u0elo2]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h4899, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h0, h1, h4899, h5767, hc12, hc23, hlam, hphi, p5783_1]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5763, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5765, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5783_1, u0elo4]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    rcases p5783_3 (m.d 0 1) (by simp) with h5809 | h5809
                                    · linarith only [h4900, h5809, hlam]
                                    · linarith only [h0, h5809, hlam]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [h5764, hlam, p5783_0]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    rcases p5783_3 (m.d 0 1) (by simp) with h5813 | h5813
                                    · linarith only [h4900, h5813, hlam]
                                    · linarith only [h4899, h5813, hlam]
                                  · have p5783_0 := h5783c.1
                                    have p5783_1 := h5783c.2.1
                                    have p5783_2 := h5783c.2.2.1
                                    have p5783_3 := h5783c.2.2.2
                                    linarith only [hlam, p5783_0]
                            · linarith only [h1, h4899, h5764, h5767, h5769, h5778, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h4899, h4900, h5767, h5769, h5774, h5777, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h5764, h5774, hlam]
                    · linarith only [h1, h4899, h5769, h5773, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5821 | h5821
            · linarith only [h1, h4899, h5764, h5821, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5823 | h5823
              · linarith only [h0, h1, h5764, h5823, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5825 | h5825
                · linarith only [h0, h5727, h5825, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5827 | h5827
                  · linarith only [h0, h1, h5761, h5764, h5827, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5829 | h5829
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5830 | h5830
                      · linarith only [h1, h4899, h5764, h5823, h5825, h5830, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h4899, h5825, h5830, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h4899, h5825, h5829, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h4899, h5763, hlam]

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4900 | h4900
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x1 m hb0 hb1 hb3 hb4 hg0 h1 h4899 h4900

end R2N4
