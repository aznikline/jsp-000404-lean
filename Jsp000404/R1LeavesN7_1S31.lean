import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg22351 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg22352 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg22353 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg22354 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg22355 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg22356 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (hg22357 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (hg22358 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (hg22359 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (hg22360 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (hg22361 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
    (h22362 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h22363 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h22364 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  have h22351 := hg22351
  have h22352 := hg22352
  have h22353 := hg22353
  have h22354 := hg22354
  have h22355 := hg22355
  have h22356 := hg22356
  have h22357 := hg22357
  have h22358 := hg22358
  have h22359 := hg22359
  have h22360 := hg22360
  have h22361 := hg22361
  rcases m.htr 3 4 5 (by decide) (by decide) with h22365 | h22365
  · rcases h0bigk with h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c | h22366c
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h0, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h15532, hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h18443, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h20697, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22372 | h22372
      · linarith only [h0, h22372, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22374 | h22374
        · rcases p22366_3 (m.d 0 3) (by simp) with h22375 | h22375
          · linarith only [h22350, h22375, hlam]
          · linarith only [h15532, h22375, hlam]
        · linarith only [h0, h22374, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22350, h22362, h22365, hc02, hc45, hlam, hphi, ht0b, ht5b, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22381 | h22381
      · linarith only [h0, h22381, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22383 | h22383
        · rcases p22366_3 (m.d 0 3) (by simp) with h22384 | h22384
          · linarith only [h22350, h22384, hlam]
          · linarith only [h22353, h22384, hlam]
        · linarith only [h22351, h22383, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22388 | h22388
      · linarith only [h0, h22388, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22390 | h22390
        · rcases p22366_3 (m.d 0 3) (by simp) with h22391 | h22391
          · linarith only [h22350, h22391, hlam]
          · linarith only [h22354, h22391, hlam]
        · linarith only [h22352, h22390, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22395 | h22395
      · linarith only [h15532, h22395, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22397 | h22397
        · rcases p22366_3 (m.d 0 3) (by simp) with h22398 | h22398
          · rcases p22366_3 (m.d 0 4) (by simp) with h22399 | h22399
            · linarith only [h22353, h22399, hlam]
            · linarith only [h18443, h22399, hlam]
          · linarith only [h15532, h22398, hlam]
        · linarith only [h0, h22397, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22350, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22406 | h22406
      · linarith only [h15532, h22406, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22408 | h22408
        · rcases p22366_3 (m.d 0 3) (by simp) with h22409 | h22409
          · rcases p22366_3 (m.d 0 4) (by simp) with h22410 | h22410
            · linarith only [h22353, h22410, hlam]
            · rcases p22366_3 (m.d 0 5) (by simp) with h22412 | h22412
              · linarith only [h22354, h22412, hlam]
              · rcases h2bigk with h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c | h22414c
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h0, hlam, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h0, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  rcases p22414_3 (m.d 0 2) (by simp) with h22418 | h22418
                  · rcases p22414_3 (m.d 1 2) (by simp) with h22419 | h22419
                    · rcases p22414_3 (m.d 2 3) (by simp) with h22420 | h22420
                      · linarith only [h22350, h22420, hlam]
                      · linarith only [h22362, h22420, hlam]
                    · linarith only [h22357, h22419, hlam]
                  · linarith only [h22418, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  rcases p22414_3 (m.d 0 2) (by simp) with h22425 | h22425
                  · rcases p22414_3 (m.d 1 2) (by simp) with h22426 | h22426
                    · rcases p22414_3 (m.d 2 3) (by simp) with h22427 | h22427
                      · linarith only [h22350, h22427, hlam]
                      · linarith only [h22363, h22427, hlam]
                    · linarith only [h22358, h22426, hlam]
                  · linarith only [h22425, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22350, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  rcases p22414_3 (m.d 0 2) (by simp) with h22435 | h22435
                  · linarith only [h0, h22435, hlam]
                  · linarith only [h22351, h22435, hlam]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  rcases p22414_3 (m.d 0 2) (by simp) with h22438 | h22438
                  · linarith only [h0, h22438, hlam]
                  · linarith only [h22352, h22438, hlam]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22350, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22356, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22350, h22362, h22365, hc02, hc45, hlam, hphi, ht0b, ht5b, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  rcases p22414_3 (m.d 0 2) (by simp) with h22445 | h22445
                  · rcases p22414_3 (m.d 1 2) (by simp) with h22446 | h22446
                    · rcases p22414_3 (m.d 2 3) (by simp) with h22447 | h22447
                      · rcases p22414_3 (m.d 2 4) (by simp) with h22448 | h22448
                        · linarith only [h22362, h22448, hlam]
                        · linarith only [h22364, h22448, hlam]
                      · linarith only [h22363, h22447, hlam]
                    · linarith only [h22358, h22446, hlam]
                  · linarith only [h22352, h22445, hlam]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22351, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22357, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22362, hlam, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h15532, h22351, h22356, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p22366_1, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22352, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22358, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22363, hlam, p22414_1]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [h22364, hlam, p22414_0]
                · have p22414_0 := h22414c.1
                  have p22414_1 := h22414c.2.1
                  have p22414_2 := h22414c.2.2.1
                  have p22414_3 := h22414c.2.2.2
                  linarith only [hlam, p22414_0]
          · linarith only [h22353, h22409, hlam]
        · linarith only [h22351, h22408, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22466 | h22466
      · linarith only [h15532, h22466, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22468 | h22468
        · rcases p22366_3 (m.d 0 3) (by simp) with h22469 | h22469
          · rcases p22366_3 (m.d 0 4) (by simp) with h22470 | h22470
            · linarith only [h22353, h22470, hlam]
            · linarith only [h22355, h22470, hlam]
          · linarith only [h22354, h22469, hlam]
        · linarith only [h22352, h22468, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22475 | h22475
      · linarith only [h18443, h22475, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22477 | h22477
        · rcases p22366_3 (m.d 0 3) (by simp) with h22478 | h22478
          · rcases p22366_3 (m.d 0 4) (by simp) with h22479 | h22479
            · rcases p22366_3 (m.d 0 5) (by simp) with h22480 | h22480
              · linarith only [h22355, h22480, hlam]
              · linarith only [h20697, h22480, hlam]
            · linarith only [h18443, h22479, hlam]
          · linarith only [h15532, h22478, hlam]
        · linarith only [h0, h22477, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22351, hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22353, hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22489 | h22489
      · linarith only [h18443, h22489, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22491 | h22491
        · rcases p22366_3 (m.d 0 3) (by simp) with h22492 | h22492
          · rcases p22366_3 (m.d 0 4) (by simp) with h22493 | h22493
            · rcases p22366_3 (m.d 0 5) (by simp) with h22494 | h22494
              · linarith only [h22355, h22494, hlam]
              · rcases h2bigk with h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c | h22496c
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h0, hlam, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h0, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22500 | h22500
                  · rcases p22496_3 (m.d 1 2) (by simp) with h22501 | h22501
                    · rcases p22496_3 (m.d 2 3) (by simp) with h22502 | h22502
                      · linarith only [h22350, h22502, hlam]
                      · linarith only [h22362, h22502, hlam]
                    · linarith only [h22357, h22501, hlam]
                  · linarith only [h22500, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22507 | h22507
                  · rcases p22496_3 (m.d 1 2) (by simp) with h22508 | h22508
                    · rcases p22496_3 (m.d 2 3) (by simp) with h22509 | h22509
                      · linarith only [h22350, h22509, hlam]
                      · linarith only [h22363, h22509, hlam]
                    · linarith only [h22358, h22508, hlam]
                  · linarith only [h22507, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22350, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22517 | h22517
                  · linarith only [h0, h22517, hlam]
                  · linarith only [h22351, h22517, hlam]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22520 | h22520
                  · linarith only [h0, h22520, hlam]
                  · linarith only [h22352, h22520, hlam]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22350, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22356, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22350, h22362, h22365, hc02, hc45, hlam, hphi, ht0b, ht5b, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22527 | h22527
                  · rcases p22496_3 (m.d 1 2) (by simp) with h22528 | h22528
                    · rcases p22496_3 (m.d 2 3) (by simp) with h22529 | h22529
                      · rcases p22496_3 (m.d 2 4) (by simp) with h22530 | h22530
                        · linarith only [h22362, h22530, hlam]
                        · linarith only [h22364, h22530, hlam]
                      · linarith only [h22363, h22529, hlam]
                    · linarith only [h22358, h22528, hlam]
                  · linarith only [h22352, h22527, hlam]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22351, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22357, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22362, hlam, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  rcases p22496_3 (m.d 0 2) (by simp) with h22540 | h22540
                  · rcases p22496_3 (m.d 1 2) (by simp) with h22541 | h22541
                    · rcases p22496_3 (m.d 2 3) (by simp) with h22542 | h22542
                      · rcases p22496_3 (m.d 2 4) (by simp) with h22543 | h22543
                        · rcases p22496_3 (m.d 2 5) (by simp) with h22544 | h22544
                          · linarith only [h22364, h22544, hlam]
                          · rcases h3bigk with h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c | h22546c
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h15532, hlam, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22362, hc03, hc25, hlam, hphi, ht0b, ht5b, p22496_1, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              rcases p22546_3 (m.d 0 3) (by simp) with h22550 | h22550
                              · rcases p22546_3 (m.d 1 3) (by simp) with h22551 | h22551
                                · rcases p22546_3 (m.d 2 3) (by simp) with h22552 | h22552
                                  · linarith only [h22350, h22552, hlam]
                                  · linarith only [h22362, h22552, hlam]
                                · linarith only [h22359, h22551, hlam]
                              · linarith only [h22550, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              rcases p22546_3 (m.d 0 3) (by simp) with h22557 | h22557
                              · rcases p22546_3 (m.d 1 3) (by simp) with h22558 | h22558
                                · rcases p22546_3 (m.d 2 3) (by simp) with h22559 | h22559
                                  · linarith only [h22350, h22559, hlam]
                                  · linarith only [h22363, h22559, hlam]
                                · linarith only [h22360, h22558, hlam]
                              · linarith only [h22557, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22350, h22356, h22362, h22363, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22496_1, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22356, h22362, h22363, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22496_1, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              rcases p22546_3 (m.d 0 3) (by simp) with h22567 | h22567
                              · linarith only [h15532, h22567, hlam]
                              · linarith only [h22353, h22567, hlam]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              rcases p22546_3 (m.d 0 3) (by simp) with h22570 | h22570
                              · linarith only [h15532, h22570, hlam]
                              · linarith only [h22354, h22570, hlam]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22350, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22356, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h0, h22350, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              rcases p22546_3 (m.d 0 3) (by simp) with h22577 | h22577
                              · rcases p22546_3 (m.d 1 3) (by simp) with h22578 | h22578
                                · rcases p22546_3 (m.d 2 3) (by simp) with h22579 | h22579
                                  · rcases p22546_3 (m.d 3 4) (by simp) with h22580 | h22580
                                    · linarith only [h22362, h22580, hlam]
                                    · linarith only [h22365, h22580, hlam]
                                  · linarith only [h22579, hlam, p22546_0]
                                · linarith only [h22360, h22578, hlam]
                              · linarith only [h22354, h22577, hlam]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22353, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22359, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22362, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h0, h22350, h22362, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22546_1]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22354, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22360, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22363, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [h22365, hlam, p22546_0]
                            · have p22546_0 := h22546c.1
                              have p22546_1 := h22546c.2.1
                              have p22546_2 := h22546c.2.2.1
                              have p22546_3 := h22546c.2.2.2
                              linarith only [hlam, p22546_0]
                        · linarith only [h22364, h22543, hlam]
                      · linarith only [h22363, h22542, hlam]
                    · linarith only [h22358, h22541, hlam]
                  · linarith only [h22352, h22540, hlam]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22352, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22358, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22363, hlam, p22496_1]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [h22364, hlam, p22496_0]
                · have p22496_0 := h22496c.1
                  have p22496_1 := h22496c.2.1
                  have p22496_2 := h22496c.2.2.1
                  have p22496_3 := h22496c.2.2.2
                  linarith only [hlam, p22496_0]
            · linarith only [h22355, h22493, hlam]
          · linarith only [h22354, h22492, hlam]
        · linarith only [h22352, h22491, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      rcases p22366_3 (m.d 0 1) (by simp) with h22608 | h22608
      · linarith only [h20697, h22608, hlam]
      · rcases p22366_3 (m.d 0 2) (by simp) with h22610 | h22610
        · rcases p22366_3 (m.d 0 3) (by simp) with h22611 | h22611
          · rcases p22366_3 (m.d 0 4) (by simp) with h22612 | h22612
            · rcases p22366_3 (m.d 0 5) (by simp) with h22613 | h22613
              · rcases h2bigk with h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c | h22614c
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h0, hlam, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h0, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22618 | h22618
                  · rcases p22614_3 (m.d 1 2) (by simp) with h22619 | h22619
                    · rcases p22614_3 (m.d 2 3) (by simp) with h22620 | h22620
                      · linarith only [h22350, h22620, hlam]
                      · linarith only [h22362, h22620, hlam]
                    · linarith only [h22357, h22619, hlam]
                  · linarith only [h22618, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22625 | h22625
                  · rcases p22614_3 (m.d 1 2) (by simp) with h22626 | h22626
                    · rcases p22614_3 (m.d 2 3) (by simp) with h22627 | h22627
                      · linarith only [h22350, h22627, hlam]
                      · linarith only [h22363, h22627, hlam]
                    · linarith only [h22358, h22626, hlam]
                  · linarith only [h22625, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22350, h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22362, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22635 | h22635
                  · linarith only [h0, h22635, hlam]
                  · linarith only [h22351, h22635, hlam]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22638 | h22638
                  · linarith only [h0, h22638, hlam]
                  · linarith only [h22352, h22638, hlam]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22350, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22356, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22350, h22362, h22365, hc02, hc45, hlam, hphi, ht0b, ht5b, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22645 | h22645
                  · rcases p22614_3 (m.d 1 2) (by simp) with h22646 | h22646
                    · rcases p22614_3 (m.d 2 3) (by simp) with h22647 | h22647
                      · rcases p22614_3 (m.d 2 4) (by simp) with h22648 | h22648
                        · linarith only [h22362, h22648, hlam]
                        · linarith only [h22364, h22648, hlam]
                      · linarith only [h22363, h22647, hlam]
                    · linarith only [h22358, h22646, hlam]
                  · linarith only [h22352, h22645, hlam]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22351, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22357, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22362, hlam, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  rcases p22614_3 (m.d 0 2) (by simp) with h22658 | h22658
                  · rcases p22614_3 (m.d 1 2) (by simp) with h22659 | h22659
                    · rcases p22614_3 (m.d 2 3) (by simp) with h22660 | h22660
                      · rcases p22614_3 (m.d 2 4) (by simp) with h22661 | h22661
                        · rcases p22614_3 (m.d 2 5) (by simp) with h22662 | h22662
                          · linarith only [h22364, h22662, hlam]
                          · rcases h3bigk with h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c | h22664c
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h15532, hlam, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22362, h22365, hc03, hc45, hlam, hphi, ht0b, ht5b, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              rcases p22664_3 (m.d 0 3) (by simp) with h22668 | h22668
                              · rcases p22664_3 (m.d 1 3) (by simp) with h22669 | h22669
                                · rcases p22664_3 (m.d 2 3) (by simp) with h22670 | h22670
                                  · linarith only [h22350, h22670, hlam]
                                  · linarith only [h22362, h22670, hlam]
                                · linarith only [h22359, h22669, hlam]
                              · linarith only [h22668, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              rcases p22664_3 (m.d 0 3) (by simp) with h22675 | h22675
                              · rcases p22664_3 (m.d 1 3) (by simp) with h22676 | h22676
                                · rcases p22664_3 (m.d 2 3) (by simp) with h22677 | h22677
                                  · linarith only [h22350, h22677, hlam]
                                  · linarith only [h22363, h22677, hlam]
                                · linarith only [h22360, h22676, hlam]
                              · linarith only [h22675, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22350, h22356, h22362, h22363, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22614_1, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22356, h22362, h22363, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22614_1, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              rcases p22664_3 (m.d 0 3) (by simp) with h22685 | h22685
                              · linarith only [h15532, h22685, hlam]
                              · linarith only [h22353, h22685, hlam]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              rcases p22664_3 (m.d 0 3) (by simp) with h22688 | h22688
                              · linarith only [h15532, h22688, hlam]
                              · linarith only [h22354, h22688, hlam]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22350, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22356, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h0, h22350, h22365, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              rcases p22664_3 (m.d 0 3) (by simp) with h22695 | h22695
                              · rcases p22664_3 (m.d 1 3) (by simp) with h22696 | h22696
                                · rcases p22664_3 (m.d 2 3) (by simp) with h22697 | h22697
                                  · rcases p22664_3 (m.d 3 4) (by simp) with h22698 | h22698
                                    · linarith only [h22362, h22698, hlam]
                                    · linarith only [h22365, h22698, hlam]
                                  · linarith only [h22697, hlam, p22664_0]
                                · linarith only [h22360, h22696, hlam]
                              · linarith only [h22354, h22695, hlam]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22353, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22359, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22362, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h0, h22350, h22362, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p22664_1]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22354, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22360, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22363, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [h22365, hlam, p22664_0]
                            · have p22664_0 := h22664c.1
                              have p22664_1 := h22664c.2.1
                              have p22664_2 := h22664c.2.2.1
                              have p22664_3 := h22664c.2.2.2
                              linarith only [hlam, p22664_0]
                        · linarith only [h22364, h22661, hlam]
                      · linarith only [h22363, h22660, hlam]
                    · linarith only [h22358, h22659, hlam]
                  · linarith only [h22352, h22658, hlam]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22352, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22358, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22363, hlam, p22614_1]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [h22364, hlam, p22614_0]
                · have p22614_0 := h22614c.1
                  have p22614_1 := h22614c.2.1
                  have p22614_2 := h22614c.2.2.1
                  have p22614_3 := h22614c.2.2.2
                  linarith only [hlam, p22614_0]
              · linarith only [h20697, h22613, hlam]
            · linarith only [h18443, h22612, hlam]
          · linarith only [h15532, h22611, hlam]
        · linarith only [h0, h22610, hlam]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22352, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22354, hlam, p22366_0]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [h22355, hlam, p22366_1]
    · have p22366_0 := h22366c.1
      have p22366_1 := h22366c.2.1
      have p22366_2 := h22366c.2.2.1
      have p22366_3 := h22366c.2.2.2
      linarith only [hlam, p22366_0]
  · rcases h0bigk with h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c | h22731c
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h0, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h15532, hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h18443, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h20697, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22737 | h22737
      · linarith only [h0, h22737, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22739 | h22739
        · rcases p22731_3 (m.d 0 3) (by simp) with h22740 | h22740
          · linarith only [h22350, h22740, hlam]
          · linarith only [h15532, h22740, hlam]
        · linarith only [h0, h22739, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h0, h22353, h22355, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h0, h22355, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22747 | h22747
      · linarith only [h0, h22747, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22749 | h22749
        · rcases p22731_3 (m.d 0 3) (by simp) with h22750 | h22750
          · linarith only [h22350, h22750, hlam]
          · linarith only [h22354, h22750, hlam]
        · linarith only [h22352, h22749, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22754 | h22754
      · linarith only [h15532, h22754, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22756 | h22756
        · rcases p22731_3 (m.d 0 3) (by simp) with h22757 | h22757
          · rcases p22731_3 (m.d 0 4) (by simp) with h22758 | h22758
            · linarith only [h22353, h22758, hlam]
            · linarith only [h18443, h22758, hlam]
          · linarith only [h15532, h22757, hlam]
        · linarith only [h0, h22756, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22350, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22351, h22364, h22365, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22766 | h22766
      · linarith only [h15532, h22766, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22768 | h22768
        · rcases p22731_3 (m.d 0 3) (by simp) with h22769 | h22769
          · rcases p22731_3 (m.d 0 4) (by simp) with h22770 | h22770
            · linarith only [h22353, h22770, hlam]
            · linarith only [h22355, h22770, hlam]
          · linarith only [h22354, h22769, hlam]
        · linarith only [h22352, h22768, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22775 | h22775
      · linarith only [h18443, h22775, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22777 | h22777
        · rcases p22731_3 (m.d 0 3) (by simp) with h22778 | h22778
          · rcases p22731_3 (m.d 0 4) (by simp) with h22779 | h22779
            · rcases p22731_3 (m.d 0 5) (by simp) with h22780 | h22780
              · linarith only [h22355, h22780, hlam]
              · linarith only [h20697, h22780, hlam]
            · linarith only [h18443, h22779, hlam]
          · linarith only [h15532, h22778, hlam]
        · linarith only [h0, h22777, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22351, hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22353, hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22789 | h22789
      · linarith only [h18443, h22789, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22791 | h22791
        · rcases p22731_3 (m.d 0 3) (by simp) with h22792 | h22792
          · rcases p22731_3 (m.d 0 4) (by simp) with h22793 | h22793
            · rcases p22731_3 (m.d 0 5) (by simp) with h22794 | h22794
              · linarith only [h22355, h22794, hlam]
              · rcases h2bigk with h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c | h22796c
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h0, hlam, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h0, h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h0, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  rcases p22796_3 (m.d 0 2) (by simp) with h22801 | h22801
                  · rcases p22796_3 (m.d 1 2) (by simp) with h22802 | h22802
                    · rcases p22796_3 (m.d 2 3) (by simp) with h22803 | h22803
                      · linarith only [h22350, h22803, hlam]
                      · linarith only [h22363, h22803, hlam]
                    · linarith only [h22358, h22802, hlam]
                  · linarith only [h22801, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22350, h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  rcases p22796_3 (m.d 0 2) (by simp) with h22812 | h22812
                  · linarith only [h0, h22812, hlam]
                  · linarith only [h22352, h22812, hlam]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22350, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22356, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22364, h22365, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22350, h22364, h22365, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22351, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22357, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22362, hlam, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h0, h22351, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22352, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22358, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22363, hlam, p22796_1]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [h22364, hlam, p22796_0]
                · have p22796_0 := h22796c.1
                  have p22796_1 := h22796c.2.1
                  have p22796_2 := h22796c.2.2.1
                  have p22796_3 := h22796c.2.2.2
                  linarith only [hlam, p22796_0]
            · linarith only [h22355, h22793, hlam]
          · linarith only [h22354, h22792, hlam]
        · linarith only [h22352, h22791, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      rcases p22731_3 (m.d 0 1) (by simp) with h22833 | h22833
      · linarith only [h20697, h22833, hlam]
      · rcases p22731_3 (m.d 0 2) (by simp) with h22835 | h22835
        · rcases p22731_3 (m.d 0 3) (by simp) with h22836 | h22836
          · rcases p22731_3 (m.d 0 4) (by simp) with h22837 | h22837
            · rcases p22731_3 (m.d 0 5) (by simp) with h22838 | h22838
              · rcases h2bigk with h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h0, hlam, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h0, h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h0, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  rcases p22839_3 (m.d 0 2) (by simp) with h22844 | h22844
                  · rcases p22839_3 (m.d 1 2) (by simp) with h22845 | h22845
                    · rcases p22839_3 (m.d 2 3) (by simp) with h22846 | h22846
                      · linarith only [h22350, h22846, hlam]
                      · linarith only [h22363, h22846, hlam]
                    · linarith only [h22358, h22845, hlam]
                  · linarith only [h22844, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22350, h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22362, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  rcases p22839_3 (m.d 0 2) (by simp) with h22855 | h22855
                  · linarith only [h0, h22855, hlam]
                  · linarith only [h22352, h22855, hlam]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22350, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22356, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22364, h22365, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h0, h22350, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22351, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22357, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22362, hlam, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h0, h22351, h22364, h22365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22352, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22358, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22363, hlam, p22839_1]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [h22364, hlam, p22839_0]
                · have p22839_0 := h22839c.1
                  have p22839_1 := h22839c.2.1
                  have p22839_2 := h22839c.2.2.1
                  have p22839_3 := h22839c.2.2.2
                  linarith only [hlam, p22839_0]
              · linarith only [h20697, h22838, hlam]
            · linarith only [h18443, h22837, hlam]
          · linarith only [h15532, h22836, hlam]
        · linarith only [h0, h22835, hlam]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22352, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22354, hlam, p22731_0]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [h22355, hlam, p22731_1]
    · have p22731_0 := h22731c.1
      have p22731_1 := h22731c.2.1
      have p22731_2 := h22731c.2.2.1
      have p22731_3 := h22731c.2.2.2
      linarith only [hlam, p22731_0]

end R2N4
