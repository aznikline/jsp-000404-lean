import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S33
import Jsp000404.R1LeavesN7_1S34

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x20 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 5) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 5) ∧ (m.d 0 1) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 1) ≤ z)))
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
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  rcases p24026_3 (m.d 0 1) (by simp) with h24432 | h24432
  · linarith only [h20697, h24432, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24434 | h24434
    · rcases p24026_3 (m.d 0 3) (by simp) with h24435 | h24435
      · rcases p24026_3 (m.d 0 4) (by simp) with h24436 | h24436
        · rcases p24026_3 (m.d 0 5) (by simp) with h24437 | h24437
          · rcases h2bigk with h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c | h24438c
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h0, hlam, p24438_1]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24441 | h24441
              · rcases p24438_3 (m.d 1 2) (by simp) with h24442 | h24442
                · rcases p24438_3 (m.d 2 3) (by simp) with h24443 | h24443
                  · linarith only [h24443, hlam, p24438_0]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24445 | h24445
                    · linarith only [h22351, h24445, hlam]
                    · linarith only [h22362, h24445, hlam]
                · linarith only [h22356, h24442, hlam]
              · linarith only [h24441, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24450 | h24450
              · rcases p24438_3 (m.d 1 2) (by simp) with h24451 | h24451
                · rcases p24438_3 (m.d 2 3) (by simp) with h24452 | h24452
                  · linarith only [h22350, h24452, hlam]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24454 | h24454
                    · linarith only [h24454, hlam, p24438_0]
                    · rcases p24438_3 (m.d 2 5) (by simp) with h24456 | h24456
                      · linarith only [h22352, h24456, hlam]
                      · rcases h3bigk with h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c | h24458c
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h15532, hlam, p24458_1]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24461 | h24461
                          · rcases p24458_3 (m.d 1 3) (by simp) with h24462 | h24462
                            · rcases p24458_3 (m.d 2 3) (by simp) with h24463 | h24463
                              · linarith only [h22350, h24463, hlam]
                              · rcases p24458_3 (m.d 3 4) (by simp) with h24465 | h24465
                                · linarith only [h22353, h24465, hlam]
                                · linarith only [h22362, h24465, hlam]
                            · linarith only [h22356, h24462, hlam]
                          · linarith only [h22350, h24461, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24470 | h24470
                          · rcases p24458_3 (m.d 1 3) (by simp) with h24471 | h24471
                            · rcases p24458_3 (m.d 2 3) (by simp) with h24472 | h24472
                              · linarith only [h22350, h24472, hlam]
                              · rcases p24458_3 (m.d 3 4) (by simp) with h24474 | h24474
                                · linarith only [h24474, hlam, p24458_0]
                                · rcases p24458_3 (m.d 3 5) (by simp) with h24476 | h24476
                                  · linarith only [h22354, h24476, hlam]
                                  · rcases h5bigk with h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c | h24478c
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h20697, hlam, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      rcases p24478_3 (m.d 0 5) (by simp) with h24481 | h24481
                                      · rcases p24478_3 (m.d 1 5) (by simp) with h24482 | h24482
                                        · rcases p24478_3 (m.d 2 5) (by simp) with h24483 | h24483
                                          · linarith only [h22352, h24483, hlam]
                                          · rcases p24478_3 (m.d 3 5) (by simp) with h24485 | h24485
                                            · linarith only [h22354, h24485, hlam]
                                            · linarith only [h23731, h24485, hlam]
                                        · linarith only [h22358, h24482, hlam]
                                      · linarith only [h22352, h24481, hlam]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h20697, h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      rcases p24478_3 (m.d 0 5) (by simp) with h24491 | h24491
                                      · rcases p24478_3 (m.d 1 5) (by simp) with h24492 | h24492
                                        · rcases p24478_3 (m.d 2 5) (by simp) with h24493 | h24493
                                          · linarith only [h22352, h24493, hlam]
                                          · linarith only [h24024, h24493, hlam]
                                        · linarith only [h22361, h24492, hlam]
                                      · linarith only [h22355, h24491, hlam]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24026_1, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      rcases p24478_3 (m.d 0 5) (by simp) with h24500 | h24500
                                      · linarith only [h20697, h24500, hlam]
                                      · linarith only [h22352, h24500, hlam]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      rcases p24478_3 (m.d 0 5) (by simp) with h24504 | h24504
                                      · linarith only [h20697, h24504, hlam]
                                      · linarith only [h22355, h24504, hlam]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22352, hlam, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22358, hlam, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h23731, hlam, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22352, hc02, hc45, hlam, hphi, ht0b, ht5b, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22354, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22360, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h15532, h22354, h22356, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h15532, h22356, h24025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24458_1, p24478_1]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22355, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h22361, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h24024, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [h24025, hlam, p24478_0]
                                    · have p24478_0 := h24478c.1
                                      have p24478_1 := h24478c.2.1
                                      have p24478_2 := h24478c.2.2.1
                                      have p24478_3 := h24478c.2.2.2
                                      linarith only [hlam, p24478_0]
                            · linarith only [h22359, h24471, hlam]
                          · linarith only [h24470, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24524 | h24524
                          · rcases p24458_3 (m.d 1 3) (by simp) with h24525 | h24525
                            · rcases p24458_3 (m.d 2 3) (by simp) with h24526 | h24526
                              · linarith only [h22350, h24526, hlam]
                              · rcases p24458_3 (m.d 3 4) (by simp) with h24528 | h24528
                                · linarith only [h22353, h24528, hlam]
                                · linarith only [h24025, h24528, hlam]
                            · linarith only [h22360, h24525, hlam]
                          · linarith only [h24524, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22354, h22356, hc01, hc12, hlam, hphi, p24026_1, p24458_1]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24535 | h24535
                          · linarith only [h15532, h24535, hlam]
                          · linarith only [h22350, h24535, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24538 | h24538
                          · linarith only [h15532, h24538, hlam]
                          · linarith only [h22353, h24538, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24541 | h24541
                          · linarith only [h15532, h24541, hlam]
                          · linarith only [h22354, h24541, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22350, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22356, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22362, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h23731, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22353, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22359, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24551 | h24551
                          · rcases p24458_3 (m.d 1 3) (by simp) with h24552 | h24552
                            · rcases p24458_3 (m.d 2 3) (by simp) with h24553 | h24553
                              · linarith only [h24553, hlam, p24458_0]
                              · rcases p24458_3 (m.d 3 4) (by simp) with h24555 | h24555
                                · rcases p24458_3 (m.d 3 5) (by simp) with h24556 | h24556
                                  · linarith only [h24025, h24556, hlam]
                                  · linarith only [h23731, h24556, hlam]
                                · linarith only [h24555, hlam, p24458_0]
                            · linarith only [h22356, h24552, hlam]
                          · linarith only [h22350, h24551, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22350, h22353, h23731, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24458_1]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22354, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h22360, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          rcases p24458_3 (m.d 0 3) (by simp) with h24566 | h24566
                          · rcases p24458_3 (m.d 1 3) (by simp) with h24567 | h24567
                            · rcases p24458_3 (m.d 2 3) (by simp) with h24568 | h24568
                              · linarith only [h24568, hlam, p24458_0]
                              · rcases p24458_3 (m.d 3 4) (by simp) with h24570 | h24570
                                · rcases p24458_3 (m.d 3 5) (by simp) with h24571 | h24571
                                  · rcases h5bigk with h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c | h24572c
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h20697, hlam, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      rcases p24572_3 (m.d 0 5) (by simp) with h24575 | h24575
                                      · rcases p24572_3 (m.d 1 5) (by simp) with h24576 | h24576
                                        · rcases p24572_3 (m.d 2 5) (by simp) with h24577 | h24577
                                          · linarith only [h22352, h24577, hlam]
                                          · rcases p24572_3 (m.d 3 5) (by simp) with h24579 | h24579
                                            · linarith only [h22354, h24579, hlam]
                                            · linarith only [h23731, h24579, hlam]
                                        · linarith only [h22358, h24576, hlam]
                                      · linarith only [h22352, h24575, hlam]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22355, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24458_1, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      rcases p24572_3 (m.d 0 5) (by simp) with h24585 | h24585
                                      · rcases p24572_3 (m.d 1 5) (by simp) with h24586 | h24586
                                        · rcases p24572_3 (m.d 2 5) (by simp) with h24587 | h24587
                                          · linarith only [h22352, h24587, hlam]
                                          · linarith only [h24024, h24587, hlam]
                                        · linarith only [h22361, h24586, hlam]
                                      · linarith only [h22355, h24585, hlam]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24026_1, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      rcases p24572_3 (m.d 0 5) (by simp) with h24594 | h24594
                                      · linarith only [h20697, h24594, hlam]
                                      · linarith only [h22352, h24594, hlam]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24458_1, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      rcases p24572_3 (m.d 0 5) (by simp) with h24598 | h24598
                                      · linarith only [h20697, h24598, hlam]
                                      · linarith only [h22355, h24598, hlam]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22352, hlam, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22358, hlam, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h23731, hlam, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h0, h22352, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22354, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22360, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h0, h22350, h22354, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h0, h22350, h22353, h24025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24572_1]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22355, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h22361, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h24024, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [h24025, hlam, p24572_0]
                                    · have p24572_0 := h24572c.1
                                      have p24572_1 := h24572c.2.1
                                      have p24572_2 := h24572c.2.2.1
                                      have p24572_3 := h24572c.2.2.2
                                      linarith only [hlam, p24572_0]
                                  · linarith only [h24571, hlam, p24458_0]
                                · linarith only [h22362, h24570, hlam]
                            · linarith only [h22356, h24567, hlam]
                          · linarith only [h22350, h24566, hlam]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [h24025, hlam, p24458_0]
                        · have p24458_0 := h24458c.1
                          have p24458_1 := h24458c.2.1
                          have p24458_2 := h24458c.2.2.1
                          have p24458_3 := h24458c.2.2.2
                          linarith only [hlam, p24458_0]
                · linarith only [h22357, h24451, hlam]
              · linarith only [h24450, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24624 | h24624
              · rcases p24438_3 (m.d 1 2) (by simp) with h24625 | h24625
                · rcases p24438_3 (m.d 2 3) (by simp) with h24626 | h24626
                  · linarith only [h22350, h24626, hlam]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24628 | h24628
                    · linarith only [h22351, h24628, hlam]
                    · linarith only [h24024, h24628, hlam]
                · linarith only [h22358, h24625, hlam]
              · linarith only [h24624, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22351, h24024, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24438_1]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24635 | h24635
              · linarith only [h0, h24635, hlam]
              · linarith only [h22350, h24635, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24638 | h24638
              · linarith only [h0, h24638, hlam]
              · linarith only [h22351, h24638, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24641 | h24641
              · linarith only [h0, h24641, hlam]
              · linarith only [h22352, h24641, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22350, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22356, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22362, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h23731, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22351, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22357, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24651 | h24651
              · rcases p24438_3 (m.d 1 2) (by simp) with h24652 | h24652
                · rcases p24438_3 (m.d 2 3) (by simp) with h24653 | h24653
                  · linarith only [h22362, h24653, hlam]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24655 | h24655
                    · rcases p24438_3 (m.d 2 5) (by simp) with h24656 | h24656
                      · linarith only [h24024, h24656, hlam]
                      · linarith only [h23731, h24656, hlam]
                    · linarith only [h22362, h24655, hlam]
                · linarith only [h22356, h24652, hlam]
              · linarith only [h22350, h24651, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24663 | h24663
              · rcases p24438_3 (m.d 1 2) (by simp) with h24664 | h24664
                · rcases p24438_3 (m.d 2 3) (by simp) with h24665 | h24665
                  · linarith only [h22362, h24665, hlam]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24667 | h24667
                    · rcases p24438_3 (m.d 2 5) (by simp) with h24668 | h24668
                      · linarith only [h24024, h24668, hlam]
                      · rcases h3bigk with h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c | h24670c
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h15532, hlam, p24670_1]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22353, h22362, h23731, hlam, p24438_1, p24670_2]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22362, h23731, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24438_1, p24670_1]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          rcases p24670_3 (m.d 0 3) (by simp) with h24675 | h24675
                          · rcases p24670_3 (m.d 1 3) (by simp) with h24676 | h24676
                            · rcases p24670_3 (m.d 2 3) (by simp) with h24677 | h24677
                              · linarith only [h22350, h24677, hlam]
                              · rcases p24670_3 (m.d 3 4) (by simp) with h24679 | h24679
                                · linarith only [h22353, h24679, hlam]
                                · linarith only [h24025, h24679, hlam]
                            · linarith only [h22360, h24676, hlam]
                          · linarith only [h24675, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22353, h22356, h22362, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24670_1]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h15532, h22353, h22362, h23731, hlam, p24438_1, p24670_2]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22362, h23731, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24670_1]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          rcases p24670_3 (m.d 0 3) (by simp) with h24688 | h24688
                          · linarith only [h15532, h24688, hlam]
                          · linarith only [h22354, h24688, hlam]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22350, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22356, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22362, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h23731, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22353, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22359, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          rcases p24670_3 (m.d 0 3) (by simp) with h24698 | h24698
                          · rcases p24670_3 (m.d 1 3) (by simp) with h24699 | h24699
                            · rcases p24670_3 (m.d 2 3) (by simp) with h24700 | h24700
                              · linarith only [h24700, hlam, p24670_0]
                              · rcases p24670_3 (m.d 3 4) (by simp) with h24702 | h24702
                                · rcases p24670_3 (m.d 3 5) (by simp) with h24703 | h24703
                                  · linarith only [h24025, h24703, hlam]
                                  · linarith only [h23731, h24703, hlam]
                                · linarith only [h24702, hlam, p24670_0]
                            · linarith only [h22356, h24699, hlam]
                          · linarith only [h22350, h24698, hlam]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22353, h23731, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24670_1]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22354, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h22360, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          rcases p24670_3 (m.d 0 3) (by simp) with h24713 | h24713
                          · rcases p24670_3 (m.d 1 3) (by simp) with h24714 | h24714
                            · rcases p24670_3 (m.d 2 3) (by simp) with h24715 | h24715
                              · linarith only [h24715, hlam, p24670_0]
                              · rcases p24670_3 (m.d 3 4) (by simp) with h24717 | h24717
                                · rcases p24670_3 (m.d 3 5) (by simp) with h24718 | h24718
                                  · rcases h5bigk with h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c | h24719c
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h20697, hlam, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      rcases p24719_3 (m.d 0 5) (by simp) with h24722 | h24722
                                      · rcases p24719_3 (m.d 1 5) (by simp) with h24723 | h24723
                                        · rcases p24719_3 (m.d 2 5) (by simp) with h24724 | h24724
                                          · linarith only [h22352, h24724, hlam]
                                          · rcases p24719_3 (m.d 3 5) (by simp) with h24726 | h24726
                                            · linarith only [h22354, h24726, hlam]
                                            · linarith only [h23731, h24726, hlam]
                                        · linarith only [h22358, h24723, hlam]
                                      · linarith only [h22352, h24722, hlam]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22355, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24670_1, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      rcases p24719_3 (m.d 0 5) (by simp) with h24732 | h24732
                                      · rcases p24719_3 (m.d 1 5) (by simp) with h24733 | h24733
                                        · rcases p24719_3 (m.d 2 5) (by simp) with h24734 | h24734
                                          · linarith only [h22352, h24734, hlam]
                                          · linarith only [h24024, h24734, hlam]
                                        · linarith only [h22361, h24733, hlam]
                                      · linarith only [h22355, h24732, hlam]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24026_1, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      rcases p24719_3 (m.d 0 5) (by simp) with h24741 | h24741
                                      · linarith only [h20697, h24741, hlam]
                                      · linarith only [h22352, h24741, hlam]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24670_1, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      rcases p24719_3 (m.d 0 5) (by simp) with h24745 | h24745
                                      · linarith only [h20697, h24745, hlam]
                                      · linarith only [h22355, h24745, hlam]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22352, hlam, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22358, hlam, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h23731, hlam, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p24438_1, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22354, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22360, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h15532, h22354, h22356, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h15532, h22353, h22356, h24025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24719_1]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22355, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h22361, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h24024, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [h24025, hlam, p24719_0]
                                    · have p24719_0 := h24719c.1
                                      have p24719_1 := h24719c.2.1
                                      have p24719_2 := h24719c.2.2.1
                                      have p24719_3 := h24719c.2.2.2
                                      linarith only [hlam, p24719_0]
                                  · linarith only [h24718, hlam, p24670_0]
                                · linarith only [h22362, h24717, hlam]
                            · linarith only [h22356, h24714, hlam]
                          · linarith only [h22350, h24713, hlam]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [h24025, hlam, p24670_0]
                        · have p24670_0 := h24670c.1
                          have p24670_1 := h24670c.2.1
                          have p24670_2 := h24670c.2.2.1
                          have p24670_3 := h24670c.2.2.2
                          linarith only [hlam, p24670_0]
                    · linarith only [h24024, h24667, hlam]
                · linarith only [h22358, h24664, hlam]
              · linarith only [h22352, h24663, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22352, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h22358, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              rcases p24438_3 (m.d 0 2) (by simp) with h24774 | h24774
              · rcases p24438_3 (m.d 1 2) (by simp) with h24775 | h24775
                · rcases p24438_3 (m.d 2 3) (by simp) with h24776 | h24776
                  · linarith only [h23731, h24776, hlam]
                  · rcases p24438_3 (m.d 2 4) (by simp) with h24778 | h24778
                    · rcases p24438_3 (m.d 2 5) (by simp) with h24779 | h24779
                      · rcases h3bigk with h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c | h24780c
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h15532, hlam, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22353, h23731, h24025, hlam, p24438_1, p24780_2]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h15532, h22356, h23731, h24025, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h15532, h22356, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22353, h22356, h23731, h24025, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h15532, h22353, h23731, h24025, hlam, p24438_1, p24780_2]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h23731, h24025, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22356, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22350, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22356, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22362, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h23731, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22353, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22359, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          rcases p24780_3 (m.d 0 3) (by simp) with h24798 | h24798
                          · rcases p24780_3 (m.d 1 3) (by simp) with h24799 | h24799
                            · rcases p24780_3 (m.d 2 3) (by simp) with h24800 | h24800
                              · linarith only [h24800, hlam, p24780_0]
                              · rcases p24780_3 (m.d 3 4) (by simp) with h24802 | h24802
                                · rcases p24780_3 (m.d 3 5) (by simp) with h24803 | h24803
                                  · linarith only [h24025, h24803, hlam]
                                  · linarith only [h23731, h24803, hlam]
                                · linarith only [h24802, hlam, p24780_0]
                            · linarith only [h22356, h24799, hlam]
                          · linarith only [h22350, h24798, hlam]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22353, h23731, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24438_1, p24780_1]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22354, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h22360, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          rcases p24780_3 (m.d 0 3) (by simp) with h24813 | h24813
                          · rcases p24780_3 (m.d 1 3) (by simp) with h24814 | h24814
                            · rcases p24780_3 (m.d 2 3) (by simp) with h24815 | h24815
                              · linarith only [h24815, hlam, p24780_0]
                              · rcases p24780_3 (m.d 3 4) (by simp) with h24817 | h24817
                                · rcases p24780_3 (m.d 3 5) (by simp) with h24818 | h24818
                                  · rcases h5bigk with h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c | h24819c
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h20697, hlam, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p24438_1, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h20697, h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      rcases p24819_3 (m.d 0 5) (by simp) with h24824 | h24824
                                      · rcases p24819_3 (m.d 1 5) (by simp) with h24825 | h24825
                                        · rcases p24819_3 (m.d 2 5) (by simp) with h24826 | h24826
                                          · linarith only [h22352, h24826, hlam]
                                          · linarith only [h24024, h24826, hlam]
                                        · linarith only [h22361, h24825, hlam]
                                      · linarith only [h22355, h24824, hlam]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc01, hc12, hlam, hphi, p24026_1, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22356, h22359, h22361, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22356, h22359, h22361, h23731, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24438_1, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      rcases p24819_3 (m.d 0 5) (by simp) with h24835 | h24835
                                      · linarith only [h20697, h24835, hlam]
                                      · linarith only [h22355, h24835, hlam]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22352, hlam, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22358, hlam, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h23731, hlam, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h0, h22352, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22354, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22360, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h15532, h22354, h22356, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h15532, h22353, h22356, h24025, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p24819_1]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22355, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h22361, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h24024, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [h24025, hlam, p24819_0]
                                    · have p24819_0 := h24819c.1
                                      have p24819_1 := h24819c.2.1
                                      have p24819_2 := h24819c.2.2.1
                                      have p24819_3 := h24819c.2.2.2
                                      linarith only [hlam, p24819_0]
                                  · linarith only [h24818, hlam, p24780_0]
                                · linarith only [h22362, h24817, hlam]
                            · linarith only [h22356, h24814, hlam]
                          · linarith only [h22350, h24813, hlam]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [h24025, hlam, p24780_0]
                        · have p24780_0 := h24780c.1
                          have p24780_1 := h24780c.2.1
                          have p24780_2 := h24780c.2.2.1
                          have p24780_3 := h24780c.2.2.2
                          linarith only [hlam, p24780_0]
                      · linarith only [h23731, h24779, hlam]
                    · linarith only [h22362, h24778, hlam]
                · linarith only [h22356, h24775, hlam]
              · linarith only [h22350, h24774, hlam]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [h24024, hlam, p24438_0]
            · have p24438_0 := h24438c.1
              have p24438_1 := h24438c.2.1
              have p24438_2 := h24438c.2.2.1
              have p24438_3 := h24438c.2.2.2
              linarith only [hlam, p24438_0]
          · linarith only [h20697, h24437, hlam]
        · linarith only [h18443, h24436, hlam]
      · linarith only [h15532, h24435, hlam]
    · linarith only [h0, h24434, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x21 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 5) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 5) ∧ (m.d 0 2) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 2) ≤ z)))
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
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22352, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x22 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 5) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 5) ∧ (m.d 0 3) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 3) ≤ z)))
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
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22354, hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x23 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 5) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 5) ∧ (m.d 0 4) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 4) ≤ z)))
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
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [h22355, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x24 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
    (h24026c : ((m.d 0 5) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 5) ∧ (m.d 0 5) - (m.d 0 5) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 5) ∨ (m.d 0 5) ≤ z)))
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
  have p24026_0 := h24026c.1
  have p24026_1 := h24026c.2.1
  have p24026_2 := h24026c.2.2.1
  have p24026_3 := h24026c.2.2.2
  linarith only [hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 3 4 + m.lam ≤ m.d 4 5 ∧ m.d 3 4 < m.d 3 5 ∧ m.d 3 5 < m.d 4 5))
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
  rcases h0bigk with h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c | h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x2 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x3 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x4 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x5 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x6 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x7 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x8 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x9 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x10 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x11 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x12 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x13 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x14 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x15 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x16 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x17 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x18 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x19 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x20 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x21 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x22 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x23 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x24 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025 h24026c

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x1 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
    (h24025 : (m.d 4 5 + m.lam ≤ m.d 3 4 ∧ m.d 4 5 < m.d 3 5 ∧ m.d 3 5 < m.d 3 4))
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
  linarith only [h22362, h24024, h24025, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0 (m : N7Model)
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
    (h22362 : (m.d 3 4 + m.lam ≤ m.d 2 3 ∧ m.d 3 4 < m.d 2 4 ∧ m.d 2 4 < m.d 2 3))
    (h23731 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
    (h24024 : (m.d 2 4 + m.lam ≤ m.d 4 5 ∧ m.d 2 4 < m.d 2 5 ∧ m.d 2 5 < m.d 4 5))
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
  rcases m.htr 3 4 5 (by decide) (by decide) with h24025 | h24025
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h23731 h24024 h24025

end R2N4
