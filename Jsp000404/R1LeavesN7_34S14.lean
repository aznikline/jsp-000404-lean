import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S11
import Jsp000404.R1LeavesN7_34S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h2407 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h3556 | h3556
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3557 | h3557
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3558 | h3558
      · linarith only [h0, h2407, h3556, h3558, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3560 | h3560
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3561 | h3561
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3562 | h3562
            · rcases h1bigk with h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c | h3563c
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h0, h2336, h3558, h3560, h4, h6, hlam, p3563_2]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                rcases p3563_3 (m.d 0 1) (by simp) with h3566 | h3566
                · rcases p3563_3 (m.d 1 2) (by simp) with h3567 | h3567
                  · linarith only [h0, h3567, hlam]
                  · rcases p3563_3 (m.d 1 3) (by simp) with h3569 | h3569
                    · linarith only [h3569, hlam, p3563_0]
                    · rcases p3563_3 (m.d 1 4) (by simp) with h3571 | h3571
                      · linarith only [h2, h3571, hlam]
                      · linarith only [h2407, h3571, hlam]
                · linarith only [h3566, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                rcases p3563_3 (m.d 0 1) (by simp) with h3575 | h3575
                · rcases p3563_3 (m.d 1 2) (by simp) with h3576 | h3576
                  · linarith only [h0, h3576, hlam]
                  · rcases p3563_3 (m.d 1 3) (by simp) with h3578 | h3578
                    · linarith only [h1, h3578, hlam]
                    · rcases p3563_3 (m.d 1 4) (by simp) with h3580 | h3580
                      · linarith only [h3580, hlam, p3563_0]
                      · rcases p3563_3 (m.d 1 5) (by simp) with h3582 | h3582
                        · linarith only [h3, h3582, hlam]
                        · rcases h3bigk with h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c | h3584c
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            rcases p3584_3 (m.d 0 3) (by simp) with h3586 | h3586
                            · rcases p3584_3 (m.d 1 3) (by simp) with h3587 | h3587
                              · linarith only [h1, h3587, hlam]
                              · rcases p3584_3 (m.d 2 3) (by simp) with h3589 | h3589
                                · linarith only [h3589, h4, hlam]
                                · linarith only [h3589, h9, hlam]
                            · linarith only [h1, h3586, hlam]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            rcases p3584_3 (m.d 0 3) (by simp) with h3593 | h3593
                            · rcases p3584_3 (m.d 1 3) (by simp) with h3594 | h3594
                              · linarith only [h1, h3594, hlam]
                              · rcases p3584_3 (m.d 2 3) (by simp) with h3596 | h3596
                                · linarith only [h3596, h4, hlam]
                                · rcases p3584_3 (m.d 3 4) (by simp) with h3598 | h3598
                                  · linarith only [h3598, h6, hlam]
                                  · linarith only [h3558, h3598, hlam]
                            · linarith only [h3593, h4, hlam]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h0, h2336, h3558, h3560, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3556, h3558, h6, h9, hlam, p3584_2]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h1, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h9, hlam, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h2407, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h2407, hc01, hc35, hlam, hphi, ht0b, ht5b, p3563_1, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h4, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3558, h6, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3558, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h0, h3558, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h6, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h0, h3556, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3584_1]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            rcases p3584_3 (m.d 0 3) (by simp) with h3618 | h3618
                            · rcases p3584_3 (m.d 1 3) (by simp) with h3619 | h3619
                              · linarith only [h2407, h3619, hlam]
                              · linarith only [h3556, h3619, hlam]
                            · linarith only [h3618, h7, hlam]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h7, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3556, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3560, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [h3562, hlam, p3584_0]
                          · have p3584_0 := h3584c.1
                            have p3584_1 := h3584c.2.1
                            have p3584_2 := h3584c.2.2.1
                            have p3584_3 := h3584c.2.2.2
                            linarith only [hlam, p3584_0]
                · linarith only [h3575, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                rcases p3563_3 (m.d 0 1) (by simp) with h3629 | h3629
                · rcases p3563_3 (m.d 1 2) (by simp) with h3630 | h3630
                  · linarith only [h0, h3630, hlam]
                  · rcases p3563_3 (m.d 1 3) (by simp) with h3632 | h3632
                    · linarith only [h1, h3632, hlam]
                    · linarith only [h3556, h3632, hlam]
                · linarith only [h3629, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h0, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h9, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h2086, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h2336, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h1, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h0, h2407, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3563_1]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h2407, hlam, p3563_1]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h0, h2407, h4, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p3563_1]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h2, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                rcases p3563_3 (m.d 0 1) (by simp) with h3647 | h3647
                · rcases p3563_3 (m.d 1 2) (by simp) with h3648 | h3648
                  · linarith only [h2086, h3648, hlam]
                  · rcases p3563_3 (m.d 1 3) (by simp) with h3650 | h3650
                    · linarith only [h2407, h3650, hlam]
                    · linarith only [h3650, h9, hlam]
                · linarith only [h0, h3647, hlam]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h2, h3556, h3562, hc01, hc45, hlam, hphi, ht0b, ht5b, p3563_1]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                rcases p3563_3 (m.d 0 1) (by simp) with h3656 | h3656
                · rcases p3563_3 (m.d 1 2) (by simp) with h3657 | h3657
                  · linarith only [h2086, h3657, hlam]
                  · rcases p3563_3 (m.d 1 3) (by simp) with h3659 | h3659
                    · linarith only [h2407, h3659, hlam]
                    · linarith only [h3556, h3659, hlam]
                · linarith only [h3, h3656, hlam]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h3, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h0, h3556, h3558, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3563_1]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h3556, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [h3557, hlam, p3563_0]
              · have p3563_0 := h3563c.1
                have p3563_1 := h3563c.2.1
                have p3563_2 := h3563c.2.2.1
                have p3563_3 := h3563c.2.2.2
                linarith only [hlam, p3563_0]
            · linarith only [h0, h3558, h3562, h4, h6, h8, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h2086, h3556, h3557, h3558, h3561, h9, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h3556, h3560, h9, hlam]
    · linarith only [h2407, h3556, h3557, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h3672 | h3672
    · rcases m.htr 2 3 4 (by decide) (by decide) with h3673 | h3673
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3674 | h3674
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3675 | h3675
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3676 | h3676
            · rcases h1bigk with h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c | h3677c
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h3556, h3673, h3676, h4, h9, hlam, p3677_2]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h3556, h3673, h3676, h4, hlam, p3677_2]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                rcases p3677_3 (m.d 0 1) (by simp) with h3681 | h3681
                · rcases p3677_3 (m.d 1 2) (by simp) with h3682 | h3682
                  · linarith only [h0, h3682, hlam]
                  · rcases p3677_3 (m.d 1 3) (by simp) with h3684 | h3684
                    · linarith only [h1, h3684, hlam]
                    · rcases p3677_3 (m.d 1 4) (by simp) with h3686 | h3686
                      · linarith only [h3686, hlam, p3677_0]
                      · rcases p3677_3 (m.d 1 5) (by simp) with h3688 | h3688
                        · linarith only [h3, h3688, hlam]
                        · rcases h3bigk with h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c | h3690c
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            rcases p3690_3 (m.d 0 3) (by simp) with h3692 | h3692
                            · rcases p3690_3 (m.d 1 3) (by simp) with h3693 | h3693
                              · linarith only [h1, h3693, hlam]
                              · rcases p3690_3 (m.d 2 3) (by simp) with h3695 | h3695
                                · linarith only [h3695, h4, hlam]
                                · linarith only [h3695, h9, hlam]
                            · linarith only [h1, h3692, hlam]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3556, h3673, h3676, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            rcases p3690_3 (m.d 0 3) (by simp) with h3700 | h3700
                            · rcases p3690_3 (m.d 1 3) (by simp) with h3701 | h3701
                              · linarith only [h1, h3701, hlam]
                              · rcases p3690_3 (m.d 2 3) (by simp) with h3703 | h3703
                                · linarith only [h3703, h4, hlam]
                                · linarith only [h3673, h3703, hlam]
                            · linarith only [h3700, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            rcases p3690_3 (m.d 0 3) (by simp) with h3707 | h3707
                            · rcases p3690_3 (m.d 1 3) (by simp) with h3708 | h3708
                              · linarith only [h1, h3708, hlam]
                              · rcases p3690_3 (m.d 2 3) (by simp) with h3710 | h3710
                                · linarith only [h3710, h4, hlam]
                                · linarith only [h3674, h3710, hlam]
                            · linarith only [h3707, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h1, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h9, hlam, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h2407, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3556, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h4, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            rcases p3690_3 (m.d 0 3) (by simp) with h3720 | h3720
                            · rcases p3690_3 (m.d 1 3) (by simp) with h3721 | h3721
                              · linarith only [h3721, h9, hlam]
                              · rcases p3690_3 (m.d 2 3) (by simp) with h3723 | h3723
                                · rcases p3690_3 (m.d 3 4) (by simp) with h3724 | h3724
                                  · linarith only [h3673, h3724, hlam]
                                  · linarith only [h2407, h3724, hlam]
                                · linarith only [h3723, h9, hlam]
                            · linarith only [h1, h3720, hlam]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3556, h3676, h9, hc12, hc23, hlam, hphi, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h0, h3556, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h6, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h0, h3673, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3673, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3556, h3673, h9, hc12, hc24, hlam, hphi, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h7, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h0, h3674, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3690_1]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3674, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [h3676, hlam, p3690_0]
                          · have p3690_0 := h3690c.1
                            have p3690_1 := h3690c.2.1
                            have p3690_2 := h3690c.2.2.1
                            have p3690_3 := h3690c.2.2.2
                            linarith only [hlam, p3690_0]
                · linarith only [h3681, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                rcases p3677_3 (m.d 0 1) (by simp) with h3743 | h3743
                · rcases p3677_3 (m.d 1 2) (by simp) with h3744 | h3744
                  · linarith only [h0, h3744, hlam]
                  · rcases p3677_3 (m.d 1 3) (by simp) with h3746 | h3746
                    · linarith only [h1, h3746, hlam]
                    · rcases p3677_3 (m.d 1 4) (by simp) with h3748 | h3748
                      · linarith only [h2, h3748, hlam]
                      · linarith only [h3672, h3748, hlam]
                · linarith only [h3743, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h9, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h2086, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h2336, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h1, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h2407, h3673, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h2407, hlam, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h3556, hlam, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h2, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h2407, h3673, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h2407, h3673, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h2407, h3673, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h3, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h3556, h3673, h3676, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h0, h3556, h3673, h3676, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3677_1]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [h3672, hlam, p3677_0]
              · have p3677_0 := h3677c.1
                have p3677_1 := h3677c.2.1
                have p3677_2 := h3677c.2.2.1
                have p3677_3 := h3677c.2.2.2
                linarith only [hlam, p3677_0]
            · linarith only [h2407, h3672, h3676, hlam]
          · linarith only [h2086, h2407, h3672, h3675, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h0, h2407, h3672, h3673, h3674, h4, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3775 | h3775
        · linarith only [h3556, h3673, h3775, h9, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h3777 | h3777
          · rcases m.htr 3 4 5 (by decide) (by decide) with h3778 | h3778
            · rcases h1bigk with h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c | h3779c
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h0, h3775, h3778, h4, h6, h9, hlam, p3779_2]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3782 | h3782
                · rcases p3779_3 (m.d 1 2) (by simp) with h3783 | h3783
                  · linarith only [h0, h3783, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3785 | h3785
                    · linarith only [h3785, hlam, p3779_0]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3787 | h3787
                      · linarith only [h2, h3787, hlam]
                      · linarith only [h2407, h3787, hlam]
                · linarith only [h3782, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3791 | h3791
                · rcases p3779_3 (m.d 1 2) (by simp) with h3792 | h3792
                  · linarith only [h0, h3792, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3794 | h3794
                    · linarith only [h1, h3794, hlam]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3796 | h3796
                      · linarith only [h3796, hlam, p3779_0]
                      · rcases p3779_3 (m.d 1 5) (by simp) with h3798 | h3798
                        · linarith only [h3, h3798, hlam]
                        · rcases h3bigk with h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c | h3800c
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            rcases p3800_3 (m.d 0 3) (by simp) with h3802 | h3802
                            · rcases p3800_3 (m.d 1 3) (by simp) with h3803 | h3803
                              · linarith only [h1, h3803, hlam]
                              · rcases p3800_3 (m.d 2 3) (by simp) with h3805 | h3805
                                · linarith only [h3805, h4, hlam]
                                · linarith only [h3805, h9, hlam]
                            · linarith only [h1, h3802, hlam]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            rcases p3800_3 (m.d 0 3) (by simp) with h3809 | h3809
                            · rcases p3800_3 (m.d 1 3) (by simp) with h3810 | h3810
                              · linarith only [h1, h3810, hlam]
                              · rcases p3800_3 (m.d 2 3) (by simp) with h3812 | h3812
                                · linarith only [h3812, h4, hlam]
                                · rcases p3800_3 (m.d 3 4) (by simp) with h3814 | h3814
                                  · linarith only [h3814, h6, hlam]
                                  · linarith only [h3673, h3814, hlam]
                            · linarith only [h3809, h4, hlam]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h0, h3775, h3778, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h0, h3775, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h1, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h9, hlam, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h2407, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h3556, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h4, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h3775, h3778, hc13, hc34, hlam, hphi, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h3673, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h3775, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h6, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            rcases p3800_3 (m.d 0 3) (by simp) with h3831 | h3831
                            · rcases p3800_3 (m.d 1 3) (by simp) with h3832 | h3832
                              · linarith only [h3832, hlam, p3800_0]
                              · rcases p3800_3 (m.d 2 3) (by simp) with h3834 | h3834
                                · linarith only [h3673, h3834, hlam]
                                · linarith only [h3834, h9, hlam]
                            · linarith only [h1, h3831, hlam]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h0, h3556, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h7, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            rcases p3800_3 (m.d 0 3) (by simp) with h3842 | h3842
                            · rcases p3800_3 (m.d 1 3) (by simp) with h3843 | h3843
                              · linarith only [h3843, hlam, p3800_0]
                              · rcases p3800_3 (m.d 2 3) (by simp) with h3845 | h3845
                                · linarith only [h3775, h3845, hlam]
                                · linarith only [h3845, h9, hlam]
                            · linarith only [h1, h3842, hlam]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p3800_1]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [h3778, hlam, p3800_0]
                          · have p3800_0 := h3800c.1
                            have p3800_1 := h3800c.2.1
                            have p3800_2 := h3800c.2.2.1
                            have p3800_3 := h3800c.2.2.2
                            linarith only [hlam, p3800_0]
                · linarith only [h3791, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3853 | h3853
                · rcases p3779_3 (m.d 1 2) (by simp) with h3854 | h3854
                  · linarith only [h0, h3854, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3856 | h3856
                    · linarith only [h1, h3856, hlam]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3858 | h3858
                      · linarith only [h2, h3858, hlam]
                      · linarith only [h3672, h3858, hlam]
                · linarith only [h3853, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h0, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h9, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h2086, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h2336, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h1, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h0, h2407, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3779_1]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h2407, hlam, p3779_1]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h3556, hlam, p3779_1]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h2, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3873 | h3873
                · rcases p3779_3 (m.d 1 2) (by simp) with h3874 | h3874
                  · linarith only [h2086, h3874, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3876 | h3876
                    · linarith only [h2407, h3876, hlam]
                    · linarith only [h3876, h9, hlam]
                · linarith only [h0, h3873, hlam]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3880 | h3880
                · rcases p3779_3 (m.d 1 2) (by simp) with h3881 | h3881
                  · linarith only [h2086, h3881, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3883 | h3883
                    · linarith only [h2407, h3883, hlam]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3885 | h3885
                      · rcases p3779_3 (m.d 1 5) (by simp) with h3886 | h3886
                        · linarith only [h3672, h3886, hlam]
                        · linarith only [h3556, h3886, hlam]
                      · linarith only [h2407, h3885, hlam]
                · linarith only [h1, h3880, hlam]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3892 | h3892
                · rcases p3779_3 (m.d 1 2) (by simp) with h3893 | h3893
                  · linarith only [h2086, h3893, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3895 | h3895
                    · linarith only [h2407, h3895, hlam]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3897 | h3897
                      · rcases p3779_3 (m.d 1 5) (by simp) with h3898 | h3898
                        · linarith only [h3672, h3898, hlam]
                        · rcases h3bigk with h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c | h3900c
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h2407, h3556, h6, hlam, p3779_1, p3900_2]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            rcases p3900_3 (m.d 0 3) (by simp) with h3903 | h3903
                            · rcases p3900_3 (m.d 1 3) (by simp) with h3904 | h3904
                              · linarith only [h1, h3904, hlam]
                              · rcases p3900_3 (m.d 2 3) (by simp) with h3906 | h3906
                                · linarith only [h3906, h4, hlam]
                                · rcases p3900_3 (m.d 3 4) (by simp) with h3908 | h3908
                                  · linarith only [h3908, h6, hlam]
                                  · linarith only [h3673, h3908, hlam]
                            · linarith only [h3903, h4, hlam]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h0, h2086, h3556, h3673, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3779_1, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h0, h3775, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h1, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h9, hlam, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h2407, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h3556, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h4, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h3775, hc13, hc35, hlam, hphi, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h3673, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h3775, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h6, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            rcases p3900_3 (m.d 0 3) (by simp) with h3925 | h3925
                            · rcases p3900_3 (m.d 1 3) (by simp) with h3926 | h3926
                              · linarith only [h3926, hlam, p3900_0]
                              · rcases p3900_3 (m.d 2 3) (by simp) with h3928 | h3928
                                · linarith only [h3673, h3928, hlam]
                                · linarith only [h3928, h9, hlam]
                            · linarith only [h1, h3925, hlam]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h0, h3556, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h7, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            rcases p3900_3 (m.d 0 3) (by simp) with h3936 | h3936
                            · rcases p3900_3 (m.d 1 3) (by simp) with h3937 | h3937
                              · linarith only [h3937, hlam, p3900_0]
                              · rcases p3900_3 (m.d 2 3) (by simp) with h3939 | h3939
                                · linarith only [h3775, h3939, hlam]
                                · linarith only [h3939, h9, hlam]
                            · linarith only [h1, h3936, hlam]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p3900_1]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [h3778, hlam, p3900_0]
                          · have p3900_0 := h3900c.1
                            have p3900_1 := h3900c.2.1
                            have p3900_2 := h3900c.2.2.1
                            have p3900_3 := h3900c.2.2.2
                            linarith only [hlam, p3900_0]
                      · linarith only [h3672, h3897, hlam]
                · linarith only [h3, h3892, hlam]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h3, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3949 | h3949
                · rcases p3779_3 (m.d 1 2) (by simp) with h3950 | h3950
                  · linarith only [h2336, h3950, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3952 | h3952
                    · linarith only [h3556, h3952, hlam]
                    · linarith only [h3952, h9, hlam]
                · linarith only [h0, h3949, hlam]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                rcases p3779_3 (m.d 0 1) (by simp) with h3956 | h3956
                · rcases p3779_3 (m.d 1 2) (by simp) with h3957 | h3957
                  · linarith only [h2336, h3957, hlam]
                  · rcases p3779_3 (m.d 1 3) (by simp) with h3959 | h3959
                    · linarith only [h3556, h3959, hlam]
                    · rcases p3779_3 (m.d 1 4) (by simp) with h3961 | h3961
                      · rcases p3779_3 (m.d 1 5) (by simp) with h3962 | h3962
                        · rcases h3bigk with h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c | h3963c
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3556, h3778, h6, hlam, p3779_1, p3963_2]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            rcases p3963_3 (m.d 0 3) (by simp) with h3966 | h3966
                            · rcases p3963_3 (m.d 1 3) (by simp) with h3967 | h3967
                              · linarith only [h1, h3967, hlam]
                              · rcases p3963_3 (m.d 2 3) (by simp) with h3969 | h3969
                                · linarith only [h3969, h4, hlam]
                                · rcases p3963_3 (m.d 3 4) (by simp) with h3971 | h3971
                                  · linarith only [h3971, h6, hlam]
                                  · linarith only [h3673, h3971, hlam]
                            · linarith only [h3966, h4, hlam]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h0, h2086, h3672, h3673, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p3779_1, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h0, h3556, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3779_1, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h1, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h9, hlam, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h2407, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3556, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h4, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3673, h9, hc12, hc34, hlam, hphi, ht23, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3673, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3775, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h6, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            rcases p3963_3 (m.d 0 3) (by simp) with h3988 | h3988
                            · rcases p3963_3 (m.d 1 3) (by simp) with h3989 | h3989
                              · linarith only [h3989, hlam, p3963_0]
                              · rcases p3963_3 (m.d 2 3) (by simp) with h3991 | h3991
                                · linarith only [h3673, h3991, hlam]
                                · linarith only [h3991, h9, hlam]
                            · linarith only [h1, h3988, hlam]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h0, h3556, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h7, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            rcases p3963_3 (m.d 0 3) (by simp) with h3999 | h3999
                            · rcases p3963_3 (m.d 1 3) (by simp) with h4000 | h4000
                              · linarith only [h4000, hlam, p3963_0]
                              · rcases p3963_3 (m.d 2 3) (by simp) with h4002 | h4002
                                · linarith only [h3775, h4002, hlam]
                                · linarith only [h4002, h9, hlam]
                            · linarith only [h1, h3999, hlam]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p3963_1]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [h3778, hlam, p3963_0]
                          · have p3963_0 := h3963c.1
                            have p3963_1 := h3963c.2.1
                            have p3963_2 := h3963c.2.2.1
                            have p3963_3 := h3963c.2.2.2
                            linarith only [hlam, p3963_0]
                        · linarith only [h3556, h3962, hlam]
                      · linarith only [h2407, h3961, hlam]
                · linarith only [h1, h3956, hlam]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [h3672, hlam, p3779_0]
              · have p3779_0 := h3779c.1
                have p3779_1 := h3779c.2.1
                have p3779_2 := h3779c.2.2.1
                have p3779_3 := h3779c.2.2.2
                linarith only [hlam, p3779_0]
            · linarith only [h2407, h3672, h3778, hlam]
          · linarith only [h2086, h3672, h3777, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h4016 | h4016
      · rcases m.htr 2 3 5 (by decide) (by decide) with h4017 | h4017
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4018 | h4018
          · rcases m.htr 3 4 5 (by decide) (by decide) with h4019 | h4019
            · linarith only [h2407, h3672, h4016, h4019, h9, hc12, hc23, hlam, hphi]
            · linarith only [h2407, h4018, h4019, h9, hc12, hc24, hlam, hphi]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h4022 | h4022
            · linarith only [h0, h2086, h4, h4018, h4022, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c | h4024c
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h2407, h4, h4016, h4018, h6, h8, h9, hlam, p4024_2]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h2407, h4, h4016, h4018, h6, h8, hlam, p4024_2]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                rcases p4024_3 (m.d 0 1) (by simp) with h4028 | h4028
                · rcases p4024_3 (m.d 1 2) (by simp) with h4029 | h4029
                  · linarith only [h0, h4029, hlam]
                  · rcases p4024_3 (m.d 1 3) (by simp) with h4031 | h4031
                    · linarith only [h1, h4031, hlam]
                    · rcases p4024_3 (m.d 1 4) (by simp) with h4033 | h4033
                      · linarith only [h4033, hlam, p4024_0]
                      · rcases p4024_3 (m.d 1 5) (by simp) with h4035 | h4035
                        · linarith only [h3, h4035, hlam]
                        · linarith only [h3672, h4035, hlam]
                · linarith only [h4028, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                rcases p4024_3 (m.d 0 1) (by simp) with h4039 | h4039
                · rcases p4024_3 (m.d 1 2) (by simp) with h4040 | h4040
                  · linarith only [h0, h4040, hlam]
                  · rcases p4024_3 (m.d 1 3) (by simp) with h4042 | h4042
                    · linarith only [h1, h4042, hlam]
                    · rcases p4024_3 (m.d 1 4) (by simp) with h4044 | h4044
                      · linarith only [h2, h4044, hlam]
                      · rcases p4024_3 (m.d 1 5) (by simp) with h4046 | h4046
                        · linarith only [h4046, hlam, p4024_0]
                        · rcases h3bigk with h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c | h4048c
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h2407, h4016, h4018, h6, h8, hlam, p4048_2]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h0, h3556, h4, h4017, hlam, p4024_2, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            rcases p4048_3 (m.d 0 3) (by simp) with h4052 | h4052
                            · rcases p4048_3 (m.d 1 3) (by simp) with h4053 | h4053
                              · linarith only [h1, h4053, hlam]
                              · rcases p4048_3 (m.d 2 3) (by simp) with h4055 | h4055
                                · linarith only [h4, h4055, hlam]
                                · linarith only [h4016, h4055, hlam]
                            · linarith only [h4052, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            rcases p4048_3 (m.d 0 3) (by simp) with h4059 | h4059
                            · rcases p4048_3 (m.d 1 3) (by simp) with h4060 | h4060
                              · linarith only [h1, h4060, hlam]
                              · rcases p4048_3 (m.d 2 3) (by simp) with h4062 | h4062
                                · linarith only [h4, h4062, hlam]
                                · linarith only [h4017, h4062, hlam]
                            · linarith only [h4059, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h1, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h9, hlam, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h2407, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h3556, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h4, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            rcases p4048_3 (m.d 0 3) (by simp) with h4072 | h4072
                            · rcases p4048_3 (m.d 1 3) (by simp) with h4073 | h4073
                              · linarith only [h4073, h9, hlam]
                              · rcases p4048_3 (m.d 2 3) (by simp) with h4075 | h4075
                                · rcases p4048_3 (m.d 3 4) (by simp) with h4076 | h4076
                                  · linarith only [h4016, h4076, hlam]
                                  · linarith only [h2407, h4076, hlam]
                                · linarith only [h4075, h9, hlam]
                            · linarith only [h1, h4072, hlam]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h2407, h9, hc12, hc23, hlam, hphi, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h0, h2407, h4, h4022, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h6, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h0, h4, h4016, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h4016, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h4022, hlam, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h7, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h0, h4, h4017, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h4017, hlam, p4048_0]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [h0, h4, h4017, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4048_1]
                          · have p4048_0 := h4048c.1
                            have p4048_1 := h4048c.2.1
                            have p4048_2 := h4048c.2.2.1
                            have p4048_3 := h4048c.2.2.2
                            linarith only [hlam, p4048_0]
                · linarith only [h4039, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h9, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h2086, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h2336, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h1, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h2407, hc12, hc34, hlam, hphi, ht23, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h2407, hlam, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h3556, hlam, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h2, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h2086, h4, h4018, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h2086, h4, h4018, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h3672, hlam, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h3, hlam, p4024_0]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h3556, h4, h4017, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h3556, h4, h4017, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [h0, h3556, h4, h4017, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4024_1]
              · have p4024_0 := h4024c.1
                have p4024_1 := h4024c.2.1
                have p4024_2 := h4024c.2.2.1
                have p4024_3 := h4024c.2.2.2
                linarith only [hlam, p4024_0]
        · linarith only [h2407, h4016, h4017, h9, hc12, hc35, hlam, hphi, ht23]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h4116 | h4116
        · linarith only [h0, h3556, h4, h4016, h4116, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4118 | h4118
          · rcases m.htr 3 4 5 (by decide) (by decide) with h4119 | h4119
            · rcases h1bigk with h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c | h4120c
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h4, h4116, h7, h9, hlam, p4120_2]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h2407, h3672, h4118, h5, hlam, p4120_2]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, hlam, p4120_2]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                rcases p4120_3 (m.d 0 1) (by simp) with h4125 | h4125
                · rcases p4120_3 (m.d 1 2) (by simp) with h4126 | h4126
                  · linarith only [h0, h4126, hlam]
                  · rcases p4120_3 (m.d 1 3) (by simp) with h4128 | h4128
                    · linarith only [h1, h4128, hlam]
                    · rcases p4120_3 (m.d 1 4) (by simp) with h4130 | h4130
                      · linarith only [h2, h4130, hlam]
                      · rcases p4120_3 (m.d 1 5) (by simp) with h4132 | h4132
                        · linarith only [h4132, hlam, p4120_0]
                        · rcases h3bigk with h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c | h4134c
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h2407, h3672, h4016, h4118, h6, hlam, p4134_2]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            rcases p4134_3 (m.d 0 3) (by simp) with h4137 | h4137
                            · rcases p4134_3 (m.d 1 3) (by simp) with h4138 | h4138
                              · linarith only [h1, h4138, hlam]
                              · rcases p4134_3 (m.d 2 3) (by simp) with h4140 | h4140
                                · linarith only [h4, h4140, hlam]
                                · rcases p4134_3 (m.d 3 4) (by simp) with h4142 | h4142
                                  · linarith only [h4142, h6, hlam]
                                  · linarith only [h4016, h4142, hlam]
                            · linarith only [h4, h4137, hlam]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h0, h2407, h3672, h4, h4016, h4118, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h0, h4, h4116, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h1, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h9, hlam, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h2407, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h3556, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h4, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h4116, h9, hc12, hc35, hlam, hphi, ht23, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h4016, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h4116, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h6, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            rcases p4134_3 (m.d 0 3) (by simp) with h4159 | h4159
                            · rcases p4134_3 (m.d 1 3) (by simp) with h4160 | h4160
                              · linarith only [h4160, hlam, p4134_0]
                              · rcases p4134_3 (m.d 2 3) (by simp) with h4162 | h4162
                                · linarith only [h4016, h4162, hlam]
                                · linarith only [h4162, h9, hlam]
                            · linarith only [h1, h4159, hlam]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h9, hc12, hc34, hlam, hphi, ht23, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h0, h3556, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h7, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            rcases p4134_3 (m.d 0 3) (by simp) with h4170 | h4170
                            · rcases p4134_3 (m.d 1 3) (by simp) with h4171 | h4171
                              · linarith only [h4171, hlam, p4134_0]
                              · rcases p4134_3 (m.d 2 3) (by simp) with h4173 | h4173
                                · linarith only [h4116, h4173, hlam]
                                · linarith only [h4173, h9, hlam]
                            · linarith only [h1, h4170, hlam]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h9, hc12, hc35, hlam, hphi, ht23, p4134_1]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [h4119, hlam, p4134_0]
                          · have p4134_0 := h4134c.1
                            have p4134_1 := h4134c.2.1
                            have p4134_2 := h4134c.2.2.1
                            have p4134_3 := h4134c.2.2.2
                            linarith only [hlam, p4134_0]
                · linarith only [h4125, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h9, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h2086, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h2336, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h1, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h2407, h3672, h4118, hc12, hc24, hlam, hphi, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h2407, hlam, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h3556, hlam, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h2, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h3672, hlam, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h3, hlam, p4120_0]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [h0, h3672, h4118, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p4120_1]
              · have p4120_0 := h4120c.1
                have p4120_1 := h4120c.2.1
                have p4120_2 := h4120c.2.2.1
                have p4120_3 := h4120c.2.2.2
                linarith only [hlam, p4120_0]
            · linarith only [h4016, h4118, h4119, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h4202 | h4202
            · linarith only [h0, h4, h4016, h4118, h4202, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h4016, h4202, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h2336 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h2407 | h2407
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336 h2407

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h2086 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h2336 | h2336
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086 h2336

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h2086 | h2086
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2086

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

set_option maxHeartbeats 8396000 in
set_option maxHeartbeats 8396000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]

set_option maxHeartbeats 8400000 in
set_option maxHeartbeats 8400000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s6 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s7 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6 h7
  · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 8404000 in
set_option maxHeartbeats 8404000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s5 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s6 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5 h6
  · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]

set_option maxHeartbeats 8408000 in
set_option maxHeartbeats 8408000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s4 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s5 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4 h5
  · linarith only [h5, hc24, hlam, hphi, ht01, ht12, u0ehi1]

set_option maxHeartbeats 8412000 in
set_option maxHeartbeats 8412000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h0ehi := hb0.1
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s4 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4
  · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]

end R2N4
