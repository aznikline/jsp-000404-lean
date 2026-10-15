import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S5
import Jsp000404.R1LeavesN7_12S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4172 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h5368 | h5368
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5369 | h5369
    · linarith only [h0, h4, h5369, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5371 | h5371
      · linarith only [h0, h3686, h5368, h5371, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5373 | h5373
        · linarith only [h1, h4101, h4172, h5369, h5373, hc02, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5375 | h5375
          · linarith only [h1, h4172, h5375, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5377 | h5377
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5378 | h5378
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5379 | h5379
                · linarith only [h1, h4172, h5377, h5379, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5381 | h5381
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5382 | h5382
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5383 | h5383
                      · rcases h1bigk with h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c | h5384c
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          rcases p5384_3 (m.d 0 1) (by simp) with h5386 | h5386
                          · rcases p5384_3 (m.d 1 2) (by simp) with h5387 | h5387
                            · linarith only [h5387, hlam, p5384_0]
                            · rcases p5384_3 (m.d 1 3) (by simp) with h5389 | h5389
                              · linarith only [h1, h5389, hlam]
                              · linarith only [h5369, h5389, hlam]
                          · linarith only [h5386, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5377, h5383, hc01, hlam, hphi, ht0b, ht5b, p5384_1, u5ehi4]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5375, h5377, h5383, hc01, hlam, hphi, ht0b, ht5b, p5384_1, u5ehi4]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          rcases p5384_3 (m.d 0 1) (by simp) with h5395 | h5395
                          · rcases p5384_3 (m.d 1 2) (by simp) with h5396 | h5396
                            · linarith only [h0, h5396, hlam]
                            · rcases p5384_3 (m.d 1 3) (by simp) with h5398 | h5398
                              · linarith only [h1, h5398, hlam]
                              · linarith only [h5377, h5398, hlam]
                          · linarith only [h5395, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h0, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5369, hlam, p5384_1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5371, hlam, p5384_1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5373, hlam, p5384_1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h1, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h1, h4, h5379, hc12, hc34, hlam, hphi, ht23, p5384_1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5375, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h1, h4, h5379, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5384_1, u5ehi1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h2, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          rcases p5384_3 (m.d 0 1) (by simp) with h5413 | h5413
                          · rcases p5384_3 (m.d 1 2) (by simp) with h5414 | h5414
                            · linarith only [h5371, h5414, hlam]
                            · rcases p5384_3 (m.d 1 3) (by simp) with h5416 | h5416
                              · linarith only [h5375, h5416, hlam]
                              · linarith only [h5369, h5416, hlam]
                          · linarith only [h0, h5413, hlam]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5377, hc14, hlam, hphi, ht01, ht0b, ht5b, p5384_1, u5ehi3]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h2, h5377, h5383, hc01, hlam, hphi, ht0b, ht5b, p5384_1, u5ehi4]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h3, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h3, h4101, h5379, h5381, hc12, hc34, hlam, hphi, ht23, p5384_1]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5377, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [h5378, hlam, p5384_0]
                        · have p5384_0 := h5384c.1
                          have p5384_1 := h5384c.2.1
                          have p5384_2 := h5384c.2.2.1
                          have p5384_3 := h5384c.2.2.2
                          linarith only [hlam, p5384_0]
                      · linarith only [h4101, h5379, h5381, h5383, hc02, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h3686, h5378, h5382, hlam]
                  · linarith only [h1, h4, h5377, h5381, hlam]
              · linarith only [h4172, h5368, h5375, h5377, h5378, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5432 | h5432
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5433 | h5433
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5434 | h5434
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5435 | h5435
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5436 | h5436
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
                          rcases p5437_3 (m.d 0 1) (by simp) with h5439 | h5439
                          · rcases p5437_3 (m.d 1 2) (by simp) with h5440 | h5440
                            · linarith only [h5440, hlam, p5437_0]
                            · rcases p5437_3 (m.d 1 3) (by simp) with h5442 | h5442
                              · linarith only [h1, h5442, hlam]
                              · linarith only [h5369, h5442, hlam]
                          · linarith only [h5439, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          rcases p5437_3 (m.d 0 1) (by simp) with h5446 | h5446
                          · rcases p5437_3 (m.d 1 2) (by simp) with h5447 | h5447
                            · linarith only [h0, h5447, hlam]
                            · rcases p5437_3 (m.d 1 3) (by simp) with h5449 | h5449
                              · linarith only [h5449, hlam, p5437_0]
                              · rcases p5437_3 (m.d 1 4) (by simp) with h5451 | h5451
                                · linarith only [h2, h5451, hlam]
                                · linarith only [h5375, h5451, hlam]
                          · linarith only [h5446, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5432, hc01, hlam, hphi, ht0b, ht5b, p5437_1, u5ehi4]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          rcases p5437_3 (m.d 0 1) (by simp) with h5456 | h5456
                          · rcases p5437_3 (m.d 1 2) (by simp) with h5457 | h5457
                            · linarith only [h0, h5457, hlam]
                            · rcases p5437_3 (m.d 1 3) (by simp) with h5459 | h5459
                              · linarith only [h1, h5459, hlam]
                              · rcases p5437_3 (m.d 1 4) (by simp) with h5461 | h5461
                                · linarith only [h2, h5461, hlam]
                                · linarith only [h5432, h5461, hlam]
                          · linarith only [h5456, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h0, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5369, hlam, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5371, hlam, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5373, hlam, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h1, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5377, hc12, hc35, hlam, hphi, ht23, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5375, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5377, hlam, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h2, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h2, h4172, h5433, hc12, hc23, hlam, hphi, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h2, h4172, h5369, h5433, hc12, hc23, hlam, hphi, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h2, h4172, h5433, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5437_1, u5ehi1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h3, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h3, h4172, h5368, h5433, hc12, hc23, hlam, hphi, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h3, h4172, h5368, h5369, h5433, hc12, hc23, hlam, hphi, p5437_1]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [h5432, hlam, p5437_0]
                        · have p5437_0 := h5437c.1
                          have p5437_1 := h5437c.2.1
                          have p5437_2 := h5437c.2.2.1
                          have p5437_3 := h5437c.2.2.2
                          linarith only [hlam, p5437_0]
                      · linarith only [h4172, h5368, h5436, hlam]
                    · linarith only [h2, h3686, h4172, h5432, h5433, h5435, hc02, hc23, hlam, hphi]
                  · linarith only [h4172, h5433, h5434, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5488 | h5488
                  · linarith only [h5369, h5377, h5433, h5488, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5490 | h5490
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5491 | h5491
                      · rcases h1bigk with h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c | h5492c
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5494 | h5494
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5495 | h5495
                            · linarith only [h5495, hlam, p5492_0]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5497 | h5497
                              · linarith only [h1, h5497, hlam]
                              · linarith only [h5369, h5497, hlam]
                          · linarith only [h5494, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5501 | h5501
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5502 | h5502
                            · linarith only [h0, h5502, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5504 | h5504
                              · linarith only [h5504, hlam, p5492_0]
                              · rcases p5492_3 (m.d 1 4) (by simp) with h5506 | h5506
                                · linarith only [h2, h5506, hlam]
                                · linarith only [h5375, h5506, hlam]
                          · linarith only [h5501, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5432, hc01, hlam, hphi, ht0b, ht5b, p5492_1, u5ehi4]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5511 | h5511
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5512 | h5512
                            · linarith only [h0, h5512, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5514 | h5514
                              · linarith only [h1, h5514, hlam]
                              · rcases p5492_3 (m.d 1 4) (by simp) with h5516 | h5516
                                · linarith only [h2, h5516, hlam]
                                · linarith only [h5432, h5516, hlam]
                          · linarith only [h5511, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h0, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5369, hlam, p5492_1]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5371, hlam, p5492_1]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5373, hlam, p5492_1]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h1, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h1, h4, h5488, h5491, hc12, hc34, hlam, hphi, ht23, p5492_1]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5375, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5377, hlam, p5492_1]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h2, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5531 | h5531
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5532 | h5532
                            · linarith only [h5371, h5532, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5534 | h5534
                              · linarith only [h5375, h5534, hlam]
                              · linarith only [h5369, h5534, hlam]
                          · linarith only [h0, h5531, hlam]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5538 | h5538
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5539 | h5539
                            · linarith only [h5371, h5539, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5541 | h5541
                              · linarith only [h5375, h5541, hlam]
                              · rcases p5492_3 (m.d 1 4) (by simp) with h5543 | h5543
                                · rcases p5492_3 (m.d 1 5) (by simp) with h5544 | h5544
                                  · linarith only [h5432, h5544, hlam]
                                  · linarith only [h5377, h5544, hlam]
                                · linarith only [h5375, h5543, hlam]
                          · linarith only [h1, h5538, hlam]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h2, h5432, hc01, hlam, hphi, ht0b, ht5b, p5492_1, u5ehi4]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h3, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5552 | h5552
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5553 | h5553
                            · linarith only [h5373, h5553, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5555 | h5555
                              · linarith only [h5377, h5555, hlam]
                              · linarith only [h5369, h5555, hlam]
                          · linarith only [h0, h5552, hlam]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          rcases p5492_3 (m.d 0 1) (by simp) with h5559 | h5559
                          · rcases p5492_3 (m.d 1 2) (by simp) with h5560 | h5560
                            · linarith only [h5373, h5560, hlam]
                            · rcases p5492_3 (m.d 1 3) (by simp) with h5562 | h5562
                              · linarith only [h5377, h5562, hlam]
                              · rcases p5492_3 (m.d 1 4) (by simp) with h5564 | h5564
                                · rcases p5492_3 (m.d 1 5) (by simp) with h5565 | h5565
                                  · rcases h2bigk with h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c | h5566c
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h4, h5488, h5491, hc12, hc34, hlam, hphi, ht23, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h4, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h3686, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h4101, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h0, hlam, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5369, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5371, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5373, hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5488, h5491, hc02, hc34, hlam, hphi, ht23, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5488, h5491, hc12, hc34, hlam, hphi, ht23, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5433, hlam, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5488, hlam, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      rcases p5566_3 (m.d 0 2) (by simp) with h5582 | h5582
                                      · linarith only [h5582, hlam, p5566_0]
                                      · rcases p5566_3 (m.d 1 2) (by simp) with h5584 | h5584
                                        · linarith only [h5371, h5584, hlam]
                                        · rcases p5566_3 (m.d 2 3) (by simp) with h5586 | h5586
                                          · linarith only [h5433, h5586, hlam]
                                          · linarith only [h4, h5586, hlam]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      rcases p5566_3 (m.d 0 2) (by simp) with h5589 | h5589
                                      · linarith only [h3686, h5589, hlam]
                                      · linarith only [h0, h5589, hlam]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [hlam, p5566_0]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h3, h4101, h5369, h5433, hc12, hc34, hlam, hphi, ht23, p5492_1, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      rcases p5566_3 (m.d 0 2) (by simp) with h5595 | h5595
                                      · linarith only [h5595, hlam, p5566_0]
                                      · rcases p5566_3 (m.d 1 2) (by simp) with h5597 | h5597
                                        · linarith only [h5373, h5597, hlam]
                                        · rcases p5566_3 (m.d 2 3) (by simp) with h5599 | h5599
                                          · linarith only [h5488, h5599, hlam]
                                          · linarith only [h4, h5599, hlam]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      rcases p5566_3 (m.d 0 2) (by simp) with h5602 | h5602
                                      · linarith only [h4101, h5602, hlam]
                                      · linarith only [h0, h5602, hlam]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [h5490, hlam, p5566_1]
                                    · have p5566_0 := h5566c.1
                                      have p5566_1 := h5566c.2.1
                                      have p5566_2 := h5566c.2.2.1
                                      have p5566_3 := h5566c.2.2.2
                                      linarith only [hlam, p5566_0]
                                  · linarith only [h5377, h5565, hlam]
                                · linarith only [h5375, h5564, hlam]
                          · linarith only [h1, h5559, hlam]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [h5432, hlam, p5492_0]
                        · have p5492_0 := h5492c.1
                          have p5492_1 := h5492c.2.1
                          have p5492_2 := h5492c.2.2.1
                          have p5492_3 := h5492c.2.2.2
                          linarith only [hlam, p5492_0]
                      · linarith only [h3686, h5368, h5433, h5491, hlam]
                    · linarith only [h2, h3686, h5368, h5432, h5490, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5615 | h5615
                · linarith only [h4172, h5368, h5369, h5375, h5432, h5615, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5617 | h5617
                  · linarith only [h5369, h5377, h5615, h5617, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5619 | h5619
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5620 | h5620
                      · rcases h1bigk with h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c | h5621c
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          rcases p5621_3 (m.d 0 1) (by simp) with h5623 | h5623
                          · rcases p5621_3 (m.d 1 2) (by simp) with h5624 | h5624
                            · linarith only [h5624, hlam, p5621_0]
                            · rcases p5621_3 (m.d 1 3) (by simp) with h5626 | h5626
                              · linarith only [h1, h5626, hlam]
                              · linarith only [h5369, h5626, hlam]
                          · linarith only [h5623, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          rcases p5621_3 (m.d 0 1) (by simp) with h5630 | h5630
                          · rcases p5621_3 (m.d 1 2) (by simp) with h5631 | h5631
                            · linarith only [h0, h5631, hlam]
                            · rcases p5621_3 (m.d 1 3) (by simp) with h5633 | h5633
                              · linarith only [h5633, hlam, p5621_0]
                              · rcases p5621_3 (m.d 1 4) (by simp) with h5635 | h5635
                                · linarith only [h2, h5635, hlam]
                                · linarith only [h5375, h5635, hlam]
                          · linarith only [h5630, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          rcases p5621_3 (m.d 0 1) (by simp) with h5639 | h5639
                          · rcases p5621_3 (m.d 1 2) (by simp) with h5640 | h5640
                            · linarith only [h0, h5640, hlam]
                            · rcases p5621_3 (m.d 1 3) (by simp) with h5642 | h5642
                              · linarith only [h1, h5642, hlam]
                              · rcases p5621_3 (m.d 1 4) (by simp) with h5644 | h5644
                                · linarith only [h5644, hlam, p5621_0]
                                · rcases p5621_3 (m.d 1 5) (by simp) with h5646 | h5646
                                  · linarith only [h3, h5646, hlam]
                                  · linarith only [h5432, h5646, hlam]
                          · linarith only [h5639, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          rcases p5621_3 (m.d 0 1) (by simp) with h5650 | h5650
                          · rcases p5621_3 (m.d 1 2) (by simp) with h5651 | h5651
                            · linarith only [h0, h5651, hlam]
                            · rcases p5621_3 (m.d 1 3) (by simp) with h5653 | h5653
                              · linarith only [h1, h5653, hlam]
                              · rcases p5621_3 (m.d 1 4) (by simp) with h5655 | h5655
                                · linarith only [h2, h5655, hlam]
                                · rcases p5621_3 (m.d 1 5) (by simp) with h5657 | h5657
                                  · linarith only [h5657, hlam, p5621_0]
                                  · rcases h2bigk with h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c | h5659c
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h4, h5617, h5620, hc12, hc34, hlam, hphi, ht23, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h4, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h3686, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h4101, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h0, hlam, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5369, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5371, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5373, hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5617, h5620, hc02, hc34, hlam, hphi, ht23, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5617, h5620, hc12, hc34, hlam, hphi, ht23, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5615, hlam, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5617, hlam, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      rcases p5659_3 (m.d 0 2) (by simp) with h5675 | h5675
                                      · linarith only [h5675, hlam, p5659_0]
                                      · rcases p5659_3 (m.d 1 2) (by simp) with h5677 | h5677
                                        · linarith only [h5371, h5677, hlam]
                                        · rcases p5659_3 (m.d 2 3) (by simp) with h5679 | h5679
                                          · linarith only [h5615, h5679, hlam]
                                          · linarith only [h4, h5679, hlam]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      rcases p5659_3 (m.d 0 2) (by simp) with h5682 | h5682
                                      · linarith only [h3686, h5682, hlam]
                                      · linarith only [h0, h5682, hlam]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h0, h4, hc12, hc24, hlam, hphi, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [hlam, p5659_0]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h0, h4101, h5615, hc12, hc34, hlam, hphi, ht23, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      rcases p5659_3 (m.d 0 2) (by simp) with h5688 | h5688
                                      · linarith only [h5688, hlam, p5659_0]
                                      · rcases p5659_3 (m.d 1 2) (by simp) with h5690 | h5690
                                        · linarith only [h5373, h5690, hlam]
                                        · rcases p5659_3 (m.d 2 3) (by simp) with h5692 | h5692
                                          · linarith only [h5617, h5692, hlam]
                                          · linarith only [h4, h5692, hlam]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      rcases p5659_3 (m.d 0 2) (by simp) with h5695 | h5695
                                      · linarith only [h4101, h5695, hlam]
                                      · linarith only [h0, h5695, hlam]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [h5619, hlam, p5659_1]
                                    · have p5659_0 := h5659c.1
                                      have p5659_1 := h5659c.2.1
                                      have p5659_2 := h5659c.2.2.1
                                      have p5659_3 := h5659c.2.2.2
                                      linarith only [hlam, p5659_0]
                          · linarith only [h5650, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h0, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5369, hlam, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5371, hlam, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5373, hlam, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h1, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5368, h5375, h5432, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5375, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5377, hlam, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h2, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3686, h5368, h5432, h5615, hc12, hc34, hlam, hphi, ht23, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3686, h5368, h5432, h5615, hc13, hc34, hlam, hphi, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h5432, hlam, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3, hlam, p5621_0]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3686, h5368, h5432, h5615, hc12, hc34, hlam, hphi, ht23, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3686, h5368, h5369, h5432, h5615, hc12, hc34, hlam, hphi, ht23, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [h3686, h5368, h5371, h5432, h5615, hc12, hc34, hlam, hphi, ht23, p5621_1]
                        · have p5621_0 := h5621c.1
                          have p5621_1 := h5621c.2.1
                          have p5621_2 := h5621c.2.2.1
                          have p5621_3 := h5621c.2.2.2
                          linarith only [hlam, p5621_0]
                      · linarith only [h3686, h5368, h5615, h5620, hlam]
                    · linarith only [h3686, h5368, h5619, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5724 | h5724
    · linarith only [h0, h4, h5724, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5726 | h5726
      · linarith only [h0, h3686, h5726, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5728 | h5728
        · linarith only [h0, h4101, h5728, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5730 | h5730
          · linarith only [h1, h4172, h5730, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5732 | h5732
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5733 | h5733
              · linarith only [h2, h5368, h5733, hlam]
              · linarith only [h5730, h5732, h5733, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5736 | h5736
              · linarith only [h2, h5368, h5736, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5738 | h5738
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5739 | h5739
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5740 | h5740
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5741 | h5741
                      · linarith only [h0, h3686, h5368, h5738, h5741, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h4, h4172, h5738, h5740, h5741, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5744 | h5744
                      · linarith only [h0, h3686, h5740, h5744, hc12, hc34, hlam, hphi, ht23]
                      · rcases h1bigk with h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          rcases p5746_3 (m.d 0 1) (by simp) with h5748 | h5748
                          · rcases p5746_3 (m.d 1 2) (by simp) with h5749 | h5749
                            · linarith only [h5749, hlam, p5746_0]
                            · rcases p5746_3 (m.d 1 3) (by simp) with h5751 | h5751
                              · linarith only [h1, h5751, hlam]
                              · linarith only [h5724, h5751, hlam]
                          · linarith only [h5748, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          rcases p5746_3 (m.d 0 1) (by simp) with h5755 | h5755
                          · rcases p5746_3 (m.d 1 2) (by simp) with h5756 | h5756
                            · linarith only [h0, h5756, hlam]
                            · rcases p5746_3 (m.d 1 3) (by simp) with h5758 | h5758
                              · linarith only [h5758, hlam, p5746_0]
                              · rcases p5746_3 (m.d 1 4) (by simp) with h5760 | h5760
                                · linarith only [h2, h5760, hlam]
                                · linarith only [h5730, h5760, hlam]
                          · linarith only [h5755, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          rcases p5746_3 (m.d 0 1) (by simp) with h5764 | h5764
                          · rcases p5746_3 (m.d 1 2) (by simp) with h5765 | h5765
                            · linarith only [h0, h5765, hlam]
                            · rcases p5746_3 (m.d 1 3) (by simp) with h5767 | h5767
                              · linarith only [h1, h5767, hlam]
                              · rcases p5746_3 (m.d 1 4) (by simp) with h5769 | h5769
                                · linarith only [h5769, hlam, p5746_0]
                                · rcases p5746_3 (m.d 1 5) (by simp) with h5771 | h5771
                                  · linarith only [h3, h5771, hlam]
                                  · linarith only [h5736, h5771, hlam]
                          · linarith only [h5764, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          rcases p5746_3 (m.d 0 1) (by simp) with h5775 | h5775
                          · rcases p5746_3 (m.d 1 2) (by simp) with h5776 | h5776
                            · linarith only [h0, h5776, hlam]
                            · rcases p5746_3 (m.d 1 3) (by simp) with h5778 | h5778
                              · linarith only [h1, h5778, hlam]
                              · rcases p5746_3 (m.d 1 4) (by simp) with h5780 | h5780
                                · linarith only [h2, h5780, hlam]
                                · rcases p5746_3 (m.d 1 5) (by simp) with h5782 | h5782
                                  · linarith only [h5782, hlam, p5746_0]
                                  · rcases h2bigk with h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c | h5784c
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h4, h4172, h5738, hc12, hc24, hlam, hphi, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h4, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h3686, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h4101, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h0, hlam, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5724, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5726, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5728, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      rcases p5784_3 (m.d 0 2) (by simp) with h5795 | h5795
                                      · linarith only [h5795, hlam, p5784_0]
                                      · rcases p5784_3 (m.d 1 2) (by simp) with h5797 | h5797
                                        · linarith only [h5724, h5797, hlam]
                                        · rcases p5784_3 (m.d 2 3) (by simp) with h5799 | h5799
                                          · rcases p5784_3 (m.d 2 4) (by simp) with h5800 | h5800
                                            · linarith only [h5738, h5800, hlam]
                                            · linarith only [h3686, h5800, hlam]
                                          · linarith only [h5799, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      rcases p5784_3 (m.d 0 2) (by simp) with h5804 | h5804
                                      · linarith only [h4, h5804, hlam]
                                      · linarith only [h0, h5804, hlam]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h3686, hc02, hc23, hlam, hphi, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h0, h4101, hc12, hc23, hlam, hphi, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h0, h5740, hc12, hc45, hlam, hphi, ht23, ht34, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5740, hc12, hc45, hlam, hphi, ht23, ht34, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5738, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5740, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      rcases p5784_3 (m.d 0 2) (by simp) with h5815 | h5815
                                      · linarith only [h5815, hlam, p5784_0]
                                      · rcases p5784_3 (m.d 1 2) (by simp) with h5817 | h5817
                                        · linarith only [h5728, h5817, hlam]
                                        · rcases p5784_3 (m.d 2 3) (by simp) with h5819 | h5819
                                          · rcases p5784_3 (m.d 2 4) (by simp) with h5820 | h5820
                                            · linarith only [h5740, h5820, hlam]
                                            · linarith only [h3686, h5820, hlam]
                                          · linarith only [h4, h5819, hlam]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      rcases p5784_3 (m.d 0 2) (by simp) with h5824 | h5824
                                      · linarith only [h4101, h5824, hlam]
                                      · linarith only [h0, h5824, hlam]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h5739, hlam, p5784_0]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [h0, h3686, hc12, hc25, hlam, hphi, p5784_1]
                                    · have p5784_0 := h5784c.1
                                      have p5784_1 := h5784c.2.1
                                      have p5784_2 := h5784c.2.2.1
                                      have p5784_3 := h5784c.2.2.2
                                      linarith only [hlam, p5784_0]
                          · linarith only [h5775, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h0, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5724, hlam, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5726, hlam, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5728, hlam, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h1, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h1, h4172, hc12, hc34, hlam, hphi, ht23, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5730, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5732, hlam, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h2, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h2, h5368, hc12, hc45, hlam, hphi, ht23, ht34, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h2, h5368, hc13, hc45, hlam, hphi, ht34, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5736, hlam, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h3, hlam, p5746_0]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5732, h5739, hc12, hc23, hlam, hphi, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5724, h5732, h5739, hc12, hc23, hlam, hphi, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [h5726, h5732, h5739, hc12, hc23, hlam, hphi, p5746_1]
                        · have p5746_0 := h5746c.1
                          have p5746_1 := h5746c.2.1
                          have p5746_2 := h5746c.2.2.1
                          have p5746_3 := h5746c.2.2.2
                          linarith only [hlam, p5746_0]
                  · linarith only [h4172, h5738, h5739, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5852 | h5852
                  · linarith only [h5724, h5732, h5738, h5852, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5854 | h5854
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5855 | h5855
                      · rcases h1bigk with h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c | h5856c
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          rcases p5856_3 (m.d 0 1) (by simp) with h5858 | h5858
                          · rcases p5856_3 (m.d 1 2) (by simp) with h5859 | h5859
                            · linarith only [h5859, hlam, p5856_0]
                            · rcases p5856_3 (m.d 1 3) (by simp) with h5861 | h5861
                              · linarith only [h1, h5861, hlam]
                              · linarith only [h5724, h5861, hlam]
                          · linarith only [h5858, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          rcases p5856_3 (m.d 0 1) (by simp) with h5865 | h5865
                          · rcases p5856_3 (m.d 1 2) (by simp) with h5866 | h5866
                            · linarith only [h0, h5866, hlam]
                            · rcases p5856_3 (m.d 1 3) (by simp) with h5868 | h5868
                              · linarith only [h5868, hlam, p5856_0]
                              · rcases p5856_3 (m.d 1 4) (by simp) with h5870 | h5870
                                · linarith only [h2, h5870, hlam]
                                · linarith only [h5730, h5870, hlam]
                          · linarith only [h5865, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          rcases p5856_3 (m.d 0 1) (by simp) with h5874 | h5874
                          · rcases p5856_3 (m.d 1 2) (by simp) with h5875 | h5875
                            · linarith only [h0, h5875, hlam]
                            · rcases p5856_3 (m.d 1 3) (by simp) with h5877 | h5877
                              · linarith only [h1, h5877, hlam]
                              · rcases p5856_3 (m.d 1 4) (by simp) with h5879 | h5879
                                · linarith only [h5879, hlam, p5856_0]
                                · rcases p5856_3 (m.d 1 5) (by simp) with h5881 | h5881
                                  · linarith only [h3, h5881, hlam]
                                  · linarith only [h5736, h5881, hlam]
                          · linarith only [h5874, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          rcases p5856_3 (m.d 0 1) (by simp) with h5885 | h5885
                          · rcases p5856_3 (m.d 1 2) (by simp) with h5886 | h5886
                            · linarith only [h0, h5886, hlam]
                            · rcases p5856_3 (m.d 1 3) (by simp) with h5888 | h5888
                              · linarith only [h1, h5888, hlam]
                              · rcases p5856_3 (m.d 1 4) (by simp) with h5890 | h5890
                                · linarith only [h2, h5890, hlam]
                                · rcases p5856_3 (m.d 1 5) (by simp) with h5892 | h5892
                                  · linarith only [h5892, hlam, p5856_0]
                                  · rcases h2bigk with h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c | h5894c
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h4, h5852, h5855, hc12, hc34, hlam, hphi, ht23, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h4, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h3686, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h4101, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h0, hlam, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5724, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5726, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5728, hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5852, h5855, hc02, hc34, hlam, hphi, ht23, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5852, h5855, hc12, hc34, hlam, hphi, ht23, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5738, hlam, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5852, hlam, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      rcases p5894_3 (m.d 0 2) (by simp) with h5910 | h5910
                                      · linarith only [h5910, hlam, p5894_0]
                                      · rcases p5894_3 (m.d 1 2) (by simp) with h5912 | h5912
                                        · linarith only [h5726, h5912, hlam]
                                        · rcases p5894_3 (m.d 2 3) (by simp) with h5914 | h5914
                                          · linarith only [h5738, h5914, hlam]
                                          · linarith only [h4, h5914, hlam]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      rcases p5894_3 (m.d 0 2) (by simp) with h5917 | h5917
                                      · linarith only [h3686, h5917, hlam]
                                      · linarith only [h0, h5917, hlam]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h0, h4, h5738, hc12, hc34, hlam, hphi, ht23, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [hlam, p5894_0]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h0, h4101, h5738, hc12, hc34, hlam, hphi, ht23, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      rcases p5894_3 (m.d 0 2) (by simp) with h5923 | h5923
                                      · linarith only [h5923, hlam, p5894_0]
                                      · rcases p5894_3 (m.d 1 2) (by simp) with h5925 | h5925
                                        · linarith only [h5728, h5925, hlam]
                                        · rcases p5894_3 (m.d 2 3) (by simp) with h5927 | h5927
                                          · linarith only [h5852, h5927, hlam]
                                          · linarith only [h4, h5927, hlam]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      rcases p5894_3 (m.d 0 2) (by simp) with h5930 | h5930
                                      · linarith only [h4101, h5930, hlam]
                                      · linarith only [h0, h5930, hlam]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [h5854, hlam, p5894_1]
                                    · have p5894_0 := h5894c.1
                                      have p5894_1 := h5894c.2.1
                                      have p5894_2 := h5894c.2.2.1
                                      have p5894_3 := h5894c.2.2.2
                                      linarith only [hlam, p5894_0]
                          · linarith only [h5885, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h0, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5724, hlam, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5726, hlam, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5728, hlam, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h1, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h2, h5368, h5730, h5738, h5854, hc12, hc34, hlam, hphi, ht23, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5730, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5732, hlam, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h2, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h2, h5368, h5738, h5854, hc12, hc34, hlam, hphi, ht23, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h2, h5368, h5738, h5854, hc13, hc34, hlam, hphi, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h5736, hlam, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h3, hlam, p5856_0]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h3, h5368, h5738, h5854, hc12, hc34, hlam, hphi, ht23, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h3, h5368, h5724, h5738, h5854, hc12, hc34, hlam, hphi, ht23, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [h3, h5368, h5726, h5738, h5854, hc12, hc34, hlam, hphi, ht23, p5856_1]
                        · have p5856_0 := h5856c.1
                          have p5856_1 := h5856c.2.1
                          have p5856_2 := h5856c.2.2.1
                          have p5856_3 := h5856c.2.2.2
                          linarith only [hlam, p5856_0]
                      · linarith only [h5738, h5854, h5855, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5958 | h5958
                      · linarith only [h0, h4, h5738, h5854, h5958, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h4, h5738, h5958, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h4101 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h4172 | h4172
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101 h4172
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101 h4172

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h3686 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h4101 | h4101
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686 h4101

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h3686 | h3686
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h3686

set_option maxHeartbeats 11914000 in
set_option maxHeartbeats 11914000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 12142000 in
set_option maxHeartbeats 12142000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s2 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s3 m hb1 hb2 hb4 hb5 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h5961 | h5961
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5962 | h5962
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5963 | h5963
        · linarith only [h0, h3, h5963, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5965 | h5965
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5966 | h5966
            · linarith only [h0, h3, h5961, h5965, h5966, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5968 | h5968
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5969 | h5969
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5970 | h5970
                  · linarith only [h0, h3, h5963, h5970, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5972 | h5972
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5973 | h5973
                      · linarith only [h1, h3, h5970, h5973, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h3, h5968, h5973, hc23, hc35, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5976 | h5976
                      · linarith only [h5961, h5965, h5972, h5976, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h3, h5961, h5965, h5972, h5976, hc13, hc35, hlam, hphi]
                · linarith only [h0, h3, h5962, h5968, h5969, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h5961, h5963, h5968, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5981 | h5981
            · linarith only [h0, h3, h5962, h5981, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h5983 | h5983
              · rcases m.htr 1 2 4 (by decide) (by decide) with h5984 | h5984
                · rcases m.htr 1 2 5 (by decide) (by decide) with h5985 | h5985
                  · linarith only [h0, h5963, h5985, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h5987 | h5987
                    · linarith only [h1, h3, h5965, h5985, h5987, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h5989 | h5989
                      · linarith only [h1, h3, h5985, h5989, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h3, h5983, h5989, hc23, hc35, hlam, hphi]
                · linarith only [h0, h3, h5962, h5983, h5984, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h5961, h5963, h5983, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5994 | h5994
        · linarith only [h2, h3, h5962, h5994, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5996 | h5996
          · linarith only [h5961, h5962, h5996, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5998 | h5998
            · linarith only [h2, h3, h5998, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6000 | h6000
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6001 | h6001
                · linarith only [h0, h5962, h6001, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6003 | h6003
                  · linarith only [h0, h3, h6003, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6005 | h6005
                    · linarith only [h1, h3, h5962, h5996, h6003, h6005, hc02, hc25, hlam, hphi]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6007 | h6007
                      · linarith only [h1, h3, h6003, h6007, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · linarith only [h0, h3, h6000, h6007, hc23, hc35, hlam, hphi]
              · linarith only [h5961, h5962, h6000, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6011 | h6011
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6012 | h6012
        · linarith only [h1, h3, h5961, h6012, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6014 | h6014
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6015 | h6015
            · linarith only [h1, h3, h5961, h6011, h6015, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6017 | h6017
              · linarith only [h0, h3, h5961, h6017, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6019 | h6019
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6020 | h6020
                  · linarith only [h0, h3, h6012, h6020, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6022 | h6022
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6023 | h6023
                      · linarith only [h1, h3, h6020, h6023, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6025 | h6025
                        · linarith only [h1, h2, h3, h5961, h6011, h6015, h6017, h6019, h6025, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1, h3, h6017, h6019, h6025, hc24, hc45, hlam, hphi]
                    · linarith only [h1, h3, h6014, h6017, h6019, h6022, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h5961, h6011, h6019, hc12, hc23, hlam, hphi]
          · linarith only [h5961, h6011, h6014, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6031 | h6031
        · linarith only [h0, h3, h6031, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6033 | h6033
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6034 | h6034
            · linarith only [h1, h3, h6033, h6034, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6036 | h6036
              · linarith only [h0, h3, h5961, h6036, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6038 | h6038
                · linarith only [h0, h6011, h6038, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6040 | h6040
                  · linarith only [h0, h3, h6031, h6040, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6042 | h6042
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6043 | h6043
                      · linarith only [h1, h3, h6040, h6043, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6045 | h6045
                        · linarith only [h1, h3, h6042, h6043, h6045, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · linarith only [h1, h3, h6042, h6045, hc34, hc45, hlam, hphi]
                    · linarith only [h1, h3, h6033, h6036, h6040, h6042, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6049 | h6049
            · linarith only [h2, h3, h6049, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6051 | h6051
              · linarith only [h0, h3, h5961, h6051, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6053 | h6053
                · linarith only [h0, h6011, h6053, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6055 | h6055
                  · linarith only [h0, h3, h6055, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6057 | h6057
                    · linarith only [h1, h3, h6033, h6055, h6057, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6059 | h6059
                      · linarith only [h2, h3, h6055, h6057, h6059, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6061 | h6061
                        · linarith only [h2, h3, h5961, h6033, h6049, h6059, h6061, hc02, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6063 | h6063
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6064 | h6064
                            · linarith only [h0, h3, h6059, h6064, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h5961, h6033, h6063, h6064, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6067 | h6067
                            · linarith only [h6051, h6059, h6063, h6067, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6069 | h6069
                              · linarith only [h2, h3, h6051, h6057, h6061, h6069, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6071 | h6071
                                · linarith only [h0, h5961, h6063, h6069, h6071, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h5961, h6063, h6071, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
