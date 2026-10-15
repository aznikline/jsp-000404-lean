import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S32

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x1 (m : N7Model)
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
    (h22363 : (m.d 3 5 + m.lam ≤ m.d 2 3 ∧ m.d 3 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 3))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h23561 | h23561
  · linarith only [h22362, h22363, h23561, hlam]
  · rcases m.htr 3 4 5 (by decide) (by decide) with h23563 | h23563
    · linarith only [h15532, h22354, h22356, h22362, h22363, h23561, h23563, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
    · rcases h0bigk with h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c | h23565c
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h0, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h15532, hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h18443, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h20697, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        rcases p23565_3 (m.d 0 1) (by simp) with h23571 | h23571
        · linarith only [h0, h23571, hlam]
        · rcases p23565_3 (m.d 0 2) (by simp) with h23573 | h23573
          · rcases p23565_3 (m.d 0 3) (by simp) with h23574 | h23574
            · linarith only [h22350, h23574, hlam]
            · linarith only [h15532, h23574, hlam]
          · linarith only [h0, h23573, hlam]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h0, h22353, h22355, h22363, h23563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h0, h22355, h22363, h23563, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h0, h22354, h22362, h22363, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        rcases p23565_3 (m.d 0 1) (by simp) with h23582 | h23582
        · linarith only [h15532, h23582, hlam]
        · rcases p23565_3 (m.d 0 2) (by simp) with h23584 | h23584
          · rcases p23565_3 (m.d 0 3) (by simp) with h23585 | h23585
            · rcases p23565_3 (m.d 0 4) (by simp) with h23586 | h23586
              · linarith only [h22353, h23586, hlam]
              · linarith only [h18443, h23586, hlam]
            · linarith only [h15532, h23585, hlam]
          · linarith only [h0, h23584, hlam]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22350, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22355, h22362, h22363, h23563, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h15532, h22355, h22356, h22362, h22363, h23563, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        rcases p23565_3 (m.d 0 1) (by simp) with h23595 | h23595
        · linarith only [h18443, h23595, hlam]
        · rcases p23565_3 (m.d 0 2) (by simp) with h23597 | h23597
          · rcases p23565_3 (m.d 0 3) (by simp) with h23598 | h23598
            · rcases p23565_3 (m.d 0 4) (by simp) with h23599 | h23599
              · rcases p23565_3 (m.d 0 5) (by simp) with h23600 | h23600
                · linarith only [h22355, h23600, hlam]
                · linarith only [h20697, h23600, hlam]
              · linarith only [h18443, h23599, hlam]
            · linarith only [h15532, h23598, hlam]
          · linarith only [h0, h23597, hlam]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22351, hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22353, hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22355, h22362, h22363, h23563, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        rcases p23565_3 (m.d 0 1) (by simp) with h23610 | h23610
        · linarith only [h20697, h23610, hlam]
        · rcases p23565_3 (m.d 0 2) (by simp) with h23612 | h23612
          · rcases p23565_3 (m.d 0 3) (by simp) with h23613 | h23613
            · rcases p23565_3 (m.d 0 4) (by simp) with h23614 | h23614
              · rcases p23565_3 (m.d 0 5) (by simp) with h23615 | h23615
                · rcases h2bigk with h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h0, hlam, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23619 | h23619
                    · rcases p23616_3 (m.d 1 2) (by simp) with h23620 | h23620
                      · rcases p23616_3 (m.d 2 3) (by simp) with h23621 | h23621
                        · linarith only [h23621, hlam, p23616_0]
                        · rcases p23616_3 (m.d 2 4) (by simp) with h23623 | h23623
                          · linarith only [h22351, h23623, hlam]
                          · rcases p23616_3 (m.d 2 5) (by simp) with h23625 | h23625
                            · linarith only [h22352, h23625, hlam]
                            · linarith only [h22363, h23625, hlam]
                      · linarith only [h22356, h23620, hlam]
                    · linarith only [h23619, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23630 | h23630
                    · rcases p23616_3 (m.d 1 2) (by simp) with h23631 | h23631
                      · rcases p23616_3 (m.d 2 3) (by simp) with h23632 | h23632
                        · linarith only [h22350, h23632, hlam]
                        · linarith only [h22362, h23632, hlam]
                      · linarith only [h22357, h23631, hlam]
                    · linarith only [h23630, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23637 | h23637
                    · rcases p23616_3 (m.d 1 2) (by simp) with h23638 | h23638
                      · rcases p23616_3 (m.d 2 3) (by simp) with h23639 | h23639
                        · linarith only [h22350, h23639, hlam]
                        · rcases p23616_3 (m.d 2 4) (by simp) with h23641 | h23641
                          · linarith only [h22351, h23641, hlam]
                          · rcases p23616_3 (m.d 2 5) (by simp) with h23643 | h23643
                            · linarith only [h23643, hlam, p23616_0]
                            · rcases h3bigk with h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c | h23645c
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h15532, hlam, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                rcases p23645_3 (m.d 0 3) (by simp) with h23648 | h23648
                                · rcases p23645_3 (m.d 1 3) (by simp) with h23649 | h23649
                                  · rcases p23645_3 (m.d 2 3) (by simp) with h23650 | h23650
                                    · linarith only [h22350, h23650, hlam]
                                    · rcases p23645_3 (m.d 3 4) (by simp) with h23652 | h23652
                                      · linarith only [h22353, h23652, hlam]
                                      · rcases p23645_3 (m.d 3 5) (by simp) with h23654 | h23654
                                        · linarith only [h22354, h23654, hlam]
                                        · linarith only [h22363, h23654, hlam]
                                  · linarith only [h22356, h23649, hlam]
                                · linarith only [h22350, h23648, hlam]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22353, h22355, h22362, h22363, h23563, hlam, p23645_2]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22350, h22362, h22363, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22353, h22355, h22356, h22362, h22363, h23563, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                rcases p23645_3 (m.d 0 3) (by simp) with h23663 | h23663
                                · linarith only [h15532, h23663, hlam]
                                · linarith only [h22350, h23663, hlam]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h15532, h22353, h22355, h22362, h22363, h23563, hlam, p23645_2]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22362, h22363, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22350, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22356, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22353, h22355, h22363, h23563, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22363, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22353, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22359, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22362, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h23563, hlam, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22354, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h22360, hlam, p23645_0]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [h0, h22350, h22353, h22355, h22362, h23563, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23645_1]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                rcases p23645_3 (m.d 0 3) (by simp) with h23681 | h23681
                                · rcases p23645_3 (m.d 1 3) (by simp) with h23682 | h23682
                                  · rcases p23645_3 (m.d 2 3) (by simp) with h23683 | h23683
                                    · linarith only [h22363, h23683, hlam]
                                    · linarith only [h22362, h23683, hlam]
                                  · linarith only [h22359, h23682, hlam]
                                · linarith only [h22353, h23681, hlam]
                              · have p23645_0 := h23645c.1
                                have p23645_1 := h23645c.2.1
                                have p23645_2 := h23645c.2.2.1
                                have p23645_3 := h23645c.2.2.2
                                linarith only [hlam, p23645_0]
                      · linarith only [h22358, h23638, hlam]
                    · linarith only [h23637, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22350, h22362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23693 | h23693
                    · linarith only [h0, h23693, hlam]
                    · linarith only [h22350, h23693, hlam]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23696 | h23696
                    · linarith only [h0, h23696, hlam]
                    · linarith only [h22351, h23696, hlam]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23699 | h23699
                    · linarith only [h0, h23699, hlam]
                    · linarith only [h22352, h23699, hlam]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22350, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22356, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22350, h22353, h22355, h22363, h23563, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22363, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22351, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22357, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22362, hlam, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h23561, hlam, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22352, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h22358, hlam, p23616_0]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [h0, h22352, h22362, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23616_1]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    rcases p23616_3 (m.d 0 2) (by simp) with h23715 | h23715
                    · rcases p23616_3 (m.d 1 2) (by simp) with h23716 | h23716
                      · rcases p23616_3 (m.d 2 3) (by simp) with h23717 | h23717
                        · linarith only [h22363, h23717, hlam]
                        · linarith only [h22362, h23717, hlam]
                      · linarith only [h22357, h23716, hlam]
                    · linarith only [h22351, h23715, hlam]
                  · have p23616_0 := h23616c.1
                    have p23616_1 := h23616c.2.1
                    have p23616_2 := h23616c.2.2.1
                    have p23616_3 := h23616c.2.2.2
                    linarith only [hlam, p23616_0]
                · linarith only [h20697, h23615, hlam]
              · linarith only [h18443, h23614, hlam]
            · linarith only [h15532, h23613, hlam]
          · linarith only [h0, h23612, hlam]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22352, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22354, hlam, p23565_0]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [h22355, hlam, p23565_1]
      · have p23565_0 := h23565c.1
        have p23565_1 := h23565c.2.1
        have p23565_2 := h23565c.2.2.1
        have p23565_3 := h23565c.2.2.2
        linarith only [hlam, p23565_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0 (m : N7Model)
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
  rcases m.htr 2 3 5 (by decide) (by decide) with h22363 | h22363
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h22363
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 hg18443 hg20697 hg22350 hg22351 hg22352 hg22353 hg22354 hg22355 hg22356 hg22357 hg22358 hg22359 hg22360 hg22361 h22362 h22363

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x0 (m : N7Model)
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
    (h23731 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
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
  rcases m.htr 2 4 5 (by decide) (by decide) with h23732 | h23732
  · rcases m.htr 3 4 5 (by decide) (by decide) with h23733 | h23733
    · rcases h0bigk with h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c | h23734c
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h0, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h15532, hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h18443, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h20697, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23740 | h23740
        · linarith only [h0, h23740, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23742 | h23742
          · rcases p23734_3 (m.d 0 3) (by simp) with h23743 | h23743
            · linarith only [h22350, h23743, hlam]
            · linarith only [h15532, h23743, hlam]
          · linarith only [h0, h23742, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h0, h22353, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h0, h22353, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23750 | h23750
        · linarith only [h0, h23750, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23752 | h23752
          · rcases p23734_3 (m.d 0 3) (by simp) with h23753 | h23753
            · linarith only [h22350, h23753, hlam]
            · linarith only [h22354, h23753, hlam]
          · linarith only [h22352, h23752, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23757 | h23757
        · linarith only [h15532, h23757, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23759 | h23759
          · rcases p23734_3 (m.d 0 3) (by simp) with h23760 | h23760
            · rcases p23734_3 (m.d 0 4) (by simp) with h23761 | h23761
              · linarith only [h22353, h23761, hlam]
              · linarith only [h18443, h23761, hlam]
            · linarith only [h15532, h23760, hlam]
          · linarith only [h0, h23759, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22350, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22353, h22362, h23731, h23733, hc03, hc45, hlam, hphi, ht0b, ht5b, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23769 | h23769
        · linarith only [h15532, h23769, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23771 | h23771
          · rcases p23734_3 (m.d 0 3) (by simp) with h23772 | h23772
            · rcases p23734_3 (m.d 0 4) (by simp) with h23773 | h23773
              · linarith only [h22353, h23773, hlam]
              · linarith only [h22355, h23773, hlam]
            · linarith only [h22354, h23772, hlam]
          · linarith only [h22352, h23771, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23778 | h23778
        · linarith only [h18443, h23778, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23780 | h23780
          · rcases p23734_3 (m.d 0 3) (by simp) with h23781 | h23781
            · rcases p23734_3 (m.d 0 4) (by simp) with h23782 | h23782
              · rcases p23734_3 (m.d 0 5) (by simp) with h23783 | h23783
                · linarith only [h22355, h23783, hlam]
                · linarith only [h20697, h23783, hlam]
              · linarith only [h18443, h23782, hlam]
            · linarith only [h15532, h23781, hlam]
          · linarith only [h0, h23780, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22351, hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22353, hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23792 | h23792
        · linarith only [h18443, h23792, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23794 | h23794
          · rcases p23734_3 (m.d 0 3) (by simp) with h23795 | h23795
            · rcases p23734_3 (m.d 0 4) (by simp) with h23796 | h23796
              · rcases p23734_3 (m.d 0 5) (by simp) with h23797 | h23797
                · linarith only [h22355, h23797, hlam]
                · rcases h2bigk with h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c | h23799c
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h0, hlam, p23799_1]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23802 | h23802
                    · rcases p23799_3 (m.d 1 2) (by simp) with h23803 | h23803
                      · rcases p23799_3 (m.d 2 3) (by simp) with h23804 | h23804
                        · linarith only [h23804, hlam, p23799_0]
                        · rcases p23799_3 (m.d 2 4) (by simp) with h23806 | h23806
                          · linarith only [h22351, h23806, hlam]
                          · linarith only [h22362, h23806, hlam]
                      · linarith only [h22356, h23803, hlam]
                    · linarith only [h23802, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23811 | h23811
                    · rcases p23799_3 (m.d 1 2) (by simp) with h23812 | h23812
                      · rcases p23799_3 (m.d 2 3) (by simp) with h23813 | h23813
                        · linarith only [h22350, h23813, hlam]
                        · rcases p23799_3 (m.d 2 4) (by simp) with h23815 | h23815
                          · linarith only [h23815, hlam, p23799_0]
                          · rcases p23799_3 (m.d 2 5) (by simp) with h23817 | h23817
                            · linarith only [h22352, h23817, hlam]
                            · rcases h3bigk with h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c | h23819c
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h15532, hlam, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                rcases p23819_3 (m.d 0 3) (by simp) with h23822 | h23822
                                · rcases p23819_3 (m.d 1 3) (by simp) with h23823 | h23823
                                  · rcases p23819_3 (m.d 2 3) (by simp) with h23824 | h23824
                                    · linarith only [h22350, h23824, hlam]
                                    · rcases p23819_3 (m.d 3 4) (by simp) with h23826 | h23826
                                      · linarith only [h22353, h23826, hlam]
                                      · linarith only [h22362, h23826, hlam]
                                  · linarith only [h22356, h23823, hlam]
                                · linarith only [h22350, h23822, hlam]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h15532, h22356, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22353, h22362, h23731, hlam, p23819_2]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22353, h22356, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                rcases p23819_3 (m.d 0 3) (by simp) with h23835 | h23835
                                · linarith only [h15532, h23835, hlam]
                                · linarith only [h22350, h23835, hlam]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22356, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h15532, h22353, h22362, h23731, hlam, p23819_2]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22350, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22356, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22362, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h0, h22362, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23799_1, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22353, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22359, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h0, h22350, h22353, h23731, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p23819_1]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                rcases p23819_3 (m.d 0 3) (by simp) with h23849 | h23849
                                · rcases p23819_3 (m.d 1 3) (by simp) with h23850 | h23850
                                  · rcases p23819_3 (m.d 2 3) (by simp) with h23851 | h23851
                                    · linarith only [h22362, h23851, hlam]
                                    · linarith only [h23731, h23851, hlam]
                                  · linarith only [h22360, h23850, hlam]
                                · linarith only [h22354, h23849, hlam]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22354, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h22360, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h23731, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [h23733, hlam, p23819_0]
                              · have p23819_0 := h23819c.1
                                have p23819_1 := h23819c.2.1
                                have p23819_2 := h23819c.2.2.1
                                have p23819_3 := h23819c.2.2.2
                                linarith only [hlam, p23819_0]
                      · linarith only [h22357, h23812, hlam]
                    · linarith only [h23811, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23863 | h23863
                    · rcases p23799_3 (m.d 1 2) (by simp) with h23864 | h23864
                      · rcases p23799_3 (m.d 2 3) (by simp) with h23865 | h23865
                        · linarith only [h22350, h23865, hlam]
                        · linarith only [h23731, h23865, hlam]
                      · linarith only [h22358, h23864, hlam]
                    · linarith only [h23863, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22350, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23799_1]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23872 | h23872
                    · linarith only [h0, h23872, hlam]
                    · linarith only [h22350, h23872, hlam]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23875 | h23875
                    · linarith only [h0, h23875, hlam]
                    · linarith only [h22351, h23875, hlam]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23878 | h23878
                    · linarith only [h0, h23878, hlam]
                    · linarith only [h22352, h23878, hlam]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22350, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22356, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22362, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22350, h22353, h22362, hc02, hc25, hlam, hphi, ht0b, ht5b, p23799_1]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22351, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22357, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h0, h22350, h22353, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23799_1]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    rcases p23799_3 (m.d 0 2) (by simp) with h23890 | h23890
                    · rcases p23799_3 (m.d 1 2) (by simp) with h23891 | h23891
                      · rcases p23799_3 (m.d 2 3) (by simp) with h23892 | h23892
                        · linarith only [h22362, h23892, hlam]
                        · linarith only [h23731, h23892, hlam]
                      · linarith only [h22358, h23891, hlam]
                    · linarith only [h22352, h23890, hlam]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22352, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h22358, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h23731, hlam, p23799_1]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [h23732, hlam, p23799_0]
                  · have p23799_0 := h23799c.1
                    have p23799_1 := h23799c.2.1
                    have p23799_2 := h23799c.2.2.1
                    have p23799_3 := h23799c.2.2.2
                    linarith only [hlam, p23799_0]
              · linarith only [h22355, h23796, hlam]
            · linarith only [h22354, h23795, hlam]
          · linarith only [h22352, h23794, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        rcases p23734_3 (m.d 0 1) (by simp) with h23905 | h23905
        · linarith only [h20697, h23905, hlam]
        · rcases p23734_3 (m.d 0 2) (by simp) with h23907 | h23907
          · rcases p23734_3 (m.d 0 3) (by simp) with h23908 | h23908
            · rcases p23734_3 (m.d 0 4) (by simp) with h23909 | h23909
              · rcases p23734_3 (m.d 0 5) (by simp) with h23910 | h23910
                · rcases h2bigk with h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c | h23911c
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h0, hlam, p23911_1]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23914 | h23914
                    · rcases p23911_3 (m.d 1 2) (by simp) with h23915 | h23915
                      · rcases p23911_3 (m.d 2 3) (by simp) with h23916 | h23916
                        · linarith only [h23916, hlam, p23911_0]
                        · rcases p23911_3 (m.d 2 4) (by simp) with h23918 | h23918
                          · linarith only [h22351, h23918, hlam]
                          · linarith only [h22362, h23918, hlam]
                      · linarith only [h22356, h23915, hlam]
                    · linarith only [h23914, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23923 | h23923
                    · rcases p23911_3 (m.d 1 2) (by simp) with h23924 | h23924
                      · rcases p23911_3 (m.d 2 3) (by simp) with h23925 | h23925
                        · linarith only [h22350, h23925, hlam]
                        · rcases p23911_3 (m.d 2 4) (by simp) with h23927 | h23927
                          · linarith only [h23927, hlam, p23911_0]
                          · rcases p23911_3 (m.d 2 5) (by simp) with h23929 | h23929
                            · linarith only [h22352, h23929, hlam]
                            · rcases h3bigk with h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c | h23931c
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h15532, hlam, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                rcases p23931_3 (m.d 0 3) (by simp) with h23934 | h23934
                                · rcases p23931_3 (m.d 1 3) (by simp) with h23935 | h23935
                                  · rcases p23931_3 (m.d 2 3) (by simp) with h23936 | h23936
                                    · linarith only [h22350, h23936, hlam]
                                    · rcases p23931_3 (m.d 3 4) (by simp) with h23938 | h23938
                                      · linarith only [h22353, h23938, hlam]
                                      · linarith only [h22362, h23938, hlam]
                                  · linarith only [h22356, h23935, hlam]
                                · linarith only [h22350, h23934, hlam]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h0, h22350, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22353, h22362, h23731, hlam, p23931_2]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22353, h22356, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                rcases p23931_3 (m.d 0 3) (by simp) with h23947 | h23947
                                · linarith only [h15532, h23947, hlam]
                                · linarith only [h22350, h23947, hlam]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22356, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h15532, h22353, h22362, h23731, hlam, p23931_2]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22350, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22356, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22362, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22353, h22362, h23733, hc03, hc45, hlam, hphi, ht0b, ht5b, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22353, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22359, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h0, h22350, h22353, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23931_1]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                rcases p23931_3 (m.d 0 3) (by simp) with h23961 | h23961
                                · rcases p23931_3 (m.d 1 3) (by simp) with h23962 | h23962
                                  · rcases p23931_3 (m.d 2 3) (by simp) with h23963 | h23963
                                    · linarith only [h22362, h23963, hlam]
                                    · linarith only [h23731, h23963, hlam]
                                  · linarith only [h22360, h23962, hlam]
                                · linarith only [h22354, h23961, hlam]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22354, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h22360, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h23731, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [h23733, hlam, p23931_0]
                              · have p23931_0 := h23931c.1
                                have p23931_1 := h23931c.2.1
                                have p23931_2 := h23931c.2.2.1
                                have p23931_3 := h23931c.2.2.2
                                linarith only [hlam, p23931_0]
                      · linarith only [h22357, h23924, hlam]
                    · linarith only [h23923, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23975 | h23975
                    · rcases p23911_3 (m.d 1 2) (by simp) with h23976 | h23976
                      · rcases p23911_3 (m.d 2 3) (by simp) with h23977 | h23977
                        · linarith only [h22350, h23977, hlam]
                        · linarith only [h23731, h23977, hlam]
                      · linarith only [h22358, h23976, hlam]
                    · linarith only [h23975, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22350, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23911_1]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23984 | h23984
                    · linarith only [h0, h23984, hlam]
                    · linarith only [h22350, h23984, hlam]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23987 | h23987
                    · linarith only [h0, h23987, hlam]
                    · linarith only [h22351, h23987, hlam]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h23990 | h23990
                    · linarith only [h0, h23990, hlam]
                    · linarith only [h22352, h23990, hlam]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22350, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22356, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22362, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22350, h22353, h22362, hc02, hc25, hlam, hphi, ht0b, ht5b, p23911_1]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22351, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22357, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h0, h22350, h22353, h22362, h23731, h23733, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23911_1]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    rcases p23911_3 (m.d 0 2) (by simp) with h24002 | h24002
                    · rcases p23911_3 (m.d 1 2) (by simp) with h24003 | h24003
                      · rcases p23911_3 (m.d 2 3) (by simp) with h24004 | h24004
                        · linarith only [h22362, h24004, hlam]
                        · linarith only [h23731, h24004, hlam]
                      · linarith only [h22358, h24003, hlam]
                    · linarith only [h22352, h24002, hlam]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22352, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h22358, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h23731, hlam, p23911_1]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [h23732, hlam, p23911_0]
                  · have p23911_0 := h23911c.1
                    have p23911_1 := h23911c.2.1
                    have p23911_2 := h23911c.2.2.1
                    have p23911_3 := h23911c.2.2.2
                    linarith only [hlam, p23911_0]
                · linarith only [h20697, h23910, hlam]
              · linarith only [h18443, h23909, hlam]
            · linarith only [h15532, h23908, hlam]
          · linarith only [h0, h23907, hlam]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22352, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22354, hlam, p23734_0]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [h22355, hlam, p23734_1]
      · have p23734_0 := h23734c.1
        have p23734_1 := h23734c.2.1
        have p23734_2 := h23734c.2.2.1
        have p23734_3 := h23734c.2.2.2
        linarith only [hlam, p23734_0]
    · linarith only [h18443, h22355, h22356, h22359, h22362, h23731, h23733, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
  · linarith only [h22362, h23731, h23732, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x0 (m : N7Model)
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
    (h24026c : ((m.d 0 1) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 1) ∧ (m.d 0 1) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 1) ≤ z)))
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
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x1 (m : N7Model)
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
    (h24026c : ((m.d 0 1) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 1) ∧ (m.d 0 2) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 2) ≤ z)))
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
  linarith only [h0, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x2 (m : N7Model)
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
    (h24026c : ((m.d 0 1) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 1) ∧ (m.d 0 3) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 3) ≤ z)))
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
  linarith only [h15532, hlam, p24026_0]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x3 (m : N7Model)
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
    (h24026c : ((m.d 0 1) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 1) ∧ (m.d 0 4) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 4) ≤ z)))
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
  linarith only [h18443, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x4 (m : N7Model)
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
    (h24026c : ((m.d 0 1) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 1) ∧ (m.d 0 5) - (m.d 0 1) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 1) ∨ (m.d 0 5) ≤ z)))
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
  linarith only [h20697, hlam, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x5 (m : N7Model)
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
    (h24026c : ((m.d 0 2) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 2) ∧ (m.d 0 1) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 1) ≤ z)))
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
  rcases p24026_3 (m.d 0 1) (by simp) with h24032 | h24032
  · linarith only [h0, h24032, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24034 | h24034
    · rcases p24026_3 (m.d 0 3) (by simp) with h24035 | h24035
      · linarith only [h22350, h24035, hlam]
      · linarith only [h15532, h24035, hlam]
    · linarith only [h0, h24034, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x6 (m : N7Model)
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
    (h24026c : ((m.d 0 2) < (m.d 0 2) ∧ 2 * m.lam ≤ (m.d 0 2) - (m.d 0 2) ∧ (m.d 0 2) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 2) ≤ z)))
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
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x7 (m : N7Model)
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
    (h24026c : ((m.d 0 2) < (m.d 0 3) ∧ 2 * m.lam ≤ (m.d 0 3) - (m.d 0 2) ∧ (m.d 0 3) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 3) ≤ z)))
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
  linarith only [h0, h22353, h23731, h24025, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24026_1]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x8 (m : N7Model)
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
    (h24026c : ((m.d 0 2) < (m.d 0 4) ∧ 2 * m.lam ≤ (m.d 0 4) - (m.d 0 2) ∧ (m.d 0 4) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 4) ≤ z)))
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
  rcases p24026_3 (m.d 0 1) (by simp) with h24041 | h24041
  · linarith only [h0, h24041, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24043 | h24043
    · rcases p24026_3 (m.d 0 3) (by simp) with h24044 | h24044
      · linarith only [h22350, h24044, hlam]
      · linarith only [h22353, h24044, hlam]
    · linarith only [h22351, h24043, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x9 (m : N7Model)
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
    (h24026c : ((m.d 0 2) < (m.d 0 5) ∧ 2 * m.lam ≤ (m.d 0 5) - (m.d 0 2) ∧ (m.d 0 5) - (m.d 0 2) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 2) ∨ (m.d 0 5) ≤ z)))
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
  rcases p24026_3 (m.d 0 1) (by simp) with h24048 | h24048
  · linarith only [h0, h24048, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24050 | h24050
    · rcases p24026_3 (m.d 0 3) (by simp) with h24051 | h24051
      · linarith only [h22350, h24051, hlam]
      · linarith only [h22354, h24051, hlam]
    · linarith only [h22352, h24050, hlam]

set_option maxHeartbeats 6108000 in
set_option maxHeartbeats 6108000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s32_x1_x1_x0_x0_x10 (m : N7Model)
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
    (h24026c : ((m.d 0 3) < (m.d 0 1) ∧ 2 * m.lam ≤ (m.d 0 1) - (m.d 0 3) ∧ (m.d 0 1) - (m.d 0 3) < 3 * m.lam ∧ (∀ z ∈ [(m.d 0 1), (m.d 0 2), (m.d 0 3), (m.d 0 4), (m.d 0 5)], z ≤ (m.d 0 3) ∨ (m.d 0 1) ≤ z)))
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
  rcases p24026_3 (m.d 0 1) (by simp) with h24055 | h24055
  · linarith only [h15532, h24055, hlam]
  · rcases p24026_3 (m.d 0 2) (by simp) with h24057 | h24057
    · rcases p24026_3 (m.d 0 3) (by simp) with h24058 | h24058
      · rcases p24026_3 (m.d 0 4) (by simp) with h24059 | h24059
        · linarith only [h22353, h24059, hlam]
        · linarith only [h18443, h24059, hlam]
      · linarith only [h15532, h24058, hlam]
    · linarith only [h0, h24057, hlam]

end R2N4
