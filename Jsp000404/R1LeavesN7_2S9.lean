import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4906 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h4907 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 5 (by decide) (by decide) with h5552 | h5552
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5553 | h5553
    · linarith only [h1, h4906, h4907, h5, h5553, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5555 | h5555
      · linarith only [h4388, h4906, h4907, h5, h5555, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5557 | h5557
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5558 | h5558
          · linarith only [h1, h4906, h5558, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5560 | h5560
            · linarith only [h1, h4388, h4906, h5560, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5562 | h5562
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5563 | h5563
                · rcases h0bigk with h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c | h5564c
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4907, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5567 | h5567
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5568 | h5568
                      · linarith only [h0, h5568, hlam]
                      · linarith only [h4, h5568, hlam]
                    · linarith only [h1, h5567, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4907, h5, h5552, h5560, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5573 | h5573
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5574 | h5574
                      · linarith only [h0, h5574, hlam]
                      · linarith only [h5574, h6, hlam]
                    · linarith only [h3, h5573, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h0, hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5580 | h5580
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5581 | h5581
                      · rcases p5564_3 (m.d 0 3) (by simp) with h5582 | h5582
                        · linarith only [h4, h5582, hlam]
                        · rcases p5564_3 (m.d 0 4) (by simp) with h5584 | h5584
                          · linarith only [h5, h5584, hlam]
                          · linarith only [h5584, h7, hlam]
                      · linarith only [h4, h5581, hlam]
                    · linarith only [h1, h5580, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4907, h5, h5552, h5560, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5590 | h5590
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5591 | h5591
                      · rcases p5564_3 (m.d 0 3) (by simp) with h5592 | h5592
                        · linarith only [h4, h5592, hlam]
                        · rcases p5564_3 (m.d 0 4) (by simp) with h5594 | h5594
                          · linarith only [h5, h5594, hlam]
                          · linarith only [h4905, h5594, hlam]
                      · linarith only [h5591, h6, hlam]
                    · linarith only [h3, h5590, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h1, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h7, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4388, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h2, hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h5, hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5606 | h5606
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5607 | h5607
                      · rcases p5564_3 (m.d 0 3) (by simp) with h5608 | h5608
                        · linarith only [h5608, h7, hlam]
                        · rcases p5564_3 (m.d 0 4) (by simp) with h5610 | h5610
                          · rcases p5564_3 (m.d 0 5) (by simp) with h5611 | h5611
                            · linarith only [h4905, h5611, hlam]
                            · linarith only [h4388, h5611, hlam]
                          · linarith only [h5610, h7, hlam]
                      · linarith only [h4, h5607, hlam]
                    · linarith only [h1, h5606, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5618 | h5618
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5619 | h5619
                      · rcases p5564_3 (m.d 0 3) (by simp) with h5620 | h5620
                        · linarith only [h5620, h7, hlam]
                        · rcases p5564_3 (m.d 0 4) (by simp) with h5622 | h5622
                          · rcases p5564_3 (m.d 0 5) (by simp) with h5623 | h5623
                            · linarith only [h4905, h5623, hlam]
                            · rcases h2bigk with h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c | h5625c
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                rcases p5625_3 (m.d 0 2) (by simp) with h5627 | h5627
                                · rcases p5625_3 (m.d 1 2) (by simp) with h5628 | h5628
                                  · linarith only [h0, h5628, hlam]
                                  · rcases p5625_3 (m.d 2 3) (by simp) with h5630 | h5630
                                    · linarith only [h4, h5630, hlam]
                                    · rcases p5625_3 (m.d 2 4) (by simp) with h5632 | h5632
                                      · linarith only [h5, h5632, hlam]
                                      · linarith only [h4907, h5632, hlam]
                                · linarith only [h0, h5627, hlam]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4907, h5, h5552, h5560, hlam, p5625_2]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4907, h5552, h5560, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5625_1]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4907, h5, h5552, hlam, p5625_2]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h0, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4907, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5625_1]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4907, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h0, h4907, h5, h5560, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5625_1]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h4906, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h5558, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h5560, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h5, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h0, h4906, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5625_1]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                rcases p5625_3 (m.d 0 2) (by simp) with h5651 | h5651
                                · rcases p5625_3 (m.d 1 2) (by simp) with h5652 | h5652
                                  · linarith only [h4907, h5652, hlam]
                                  · linarith only [h4906, h5652, hlam]
                                · linarith only [h4, h5651, hlam]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                rcases p5625_3 (m.d 0 2) (by simp) with h5657 | h5657
                                · rcases p5625_3 (m.d 1 2) (by simp) with h5658 | h5658
                                  · linarith only [h4907, h5658, hlam]
                                  · linarith only [h5552, h5658, hlam]
                                · linarith only [h5657, h6, hlam]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h6, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h5552, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h0, h5552, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5625_1]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [h5562, hlam, p5625_0]
                              · have p5625_0 := h5625c.1
                                have p5625_1 := h5625c.2.1
                                have p5625_2 := h5625c.2.2.1
                                have p5625_3 := h5625c.2.2.2
                                linarith only [hlam, p5625_0]
                          · linarith only [h4905, h5622, hlam]
                      · linarith only [h5619, h6, hlam]
                    · linarith only [h3, h5618, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h3, hlam, p5564_0]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h6, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    rcases p5564_3 (m.d 0 1) (by simp) with h5672 | h5672
                    · rcases p5564_3 (m.d 0 2) (by simp) with h5673 | h5673
                      · rcases p5564_3 (m.d 0 3) (by simp) with h5674 | h5674
                        · linarith only [h4388, h5674, hlam]
                        · rcases p5564_3 (m.d 0 4) (by simp) with h5676 | h5676
                          · rcases p5564_3 (m.d 0 5) (by simp) with h5677 | h5677
                            · rcases h2bigk with h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c | h5678c
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                rcases p5678_3 (m.d 0 2) (by simp) with h5680 | h5680
                                · rcases p5678_3 (m.d 1 2) (by simp) with h5681 | h5681
                                  · linarith only [h0, h5681, hlam]
                                  · rcases p5678_3 (m.d 2 3) (by simp) with h5683 | h5683
                                    · linarith only [h4, h5683, hlam]
                                    · rcases p5678_3 (m.d 2 4) (by simp) with h5685 | h5685
                                      · linarith only [h5, h5685, hlam]
                                      · linarith only [h4907, h5685, hlam]
                                · linarith only [h0, h5680, hlam]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4906, h4907, h5, hlam, p5678_2]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h0, h4907, h5552, hc01, hc25, hlam, hphi, ht0b, ht5b, p5678_1]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4907, h5, h5552, hlam, p5678_2]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h0, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h0, h4907, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5678_1]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4907, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h0, h4907, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p5678_1]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4906, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h5558, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h5560, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h5, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h4906, h5, h7, hc23, hc34, hlam, hphi, p5678_1]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                rcases p5678_3 (m.d 0 2) (by simp) with h5704 | h5704
                                · rcases p5678_3 (m.d 1 2) (by simp) with h5705 | h5705
                                  · linarith only [h4907, h5705, hlam]
                                  · linarith only [h4906, h5705, hlam]
                                · linarith only [h4, h5704, hlam]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                rcases p5678_3 (m.d 0 2) (by simp) with h5710 | h5710
                                · rcases p5678_3 (m.d 1 2) (by simp) with h5711 | h5711
                                  · linarith only [h4907, h5711, hlam]
                                  · linarith only [h5552, h5711, hlam]
                                · linarith only [h5710, h6, hlam]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h6, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h5552, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h0, h5552, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5678_1]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [h5562, hlam, p5678_0]
                              · have p5678_0 := h5678c.1
                                have p5678_1 := h5678c.2.1
                                have p5678_2 := h5678c.2.2.1
                                have p5678_3 := h5678c.2.2.2
                                linarith only [hlam, p5678_0]
                            · linarith only [h4388, h5677, hlam]
                          · linarith only [h5676, h7, hlam]
                      · linarith only [h4, h5673, hlam]
                    · linarith only [h1, h5672, hlam]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [h4905, hlam, p5564_1]
                  · have p5564_0 := h5564c.1
                    have p5564_1 := h5564c.2.1
                    have p5564_2 := h5564c.2.2.1
                    have p5564_3 := h5564c.2.2.2
                    linarith only [hlam, p5564_0]
                · linarith only [h4905, h5563, h7, hlam]
              · linarith only [h4907, h5552, h5560, h5562, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h4905, h4906, h4907, h5557, h7, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h5729 | h5729
    · linarith only [h1, h4906, h4907, h5, h5729, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h5731 | h5731
      · linarith only [h1, h4388, h5731, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h5733 | h5733
        · rcases m.htr 2 3 4 (by decide) (by decide) with h5734 | h5734
          · linarith only [h1, h4906, h5734, h7, hlam]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h5736 | h5736
            · linarith only [h4388, h4906, h5552, h5736, h6, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h5738 | h5738
              · rcases m.htr 3 4 5 (by decide) (by decide) with h5739 | h5739
                · rcases h0bigk with h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c | h5740c
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h5, h5552, h5738, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    rcases p5740_3 (m.d 0 1) (by simp) with h5743 | h5743
                    · rcases p5740_3 (m.d 0 2) (by simp) with h5744 | h5744
                      · linarith only [h0, h5744, hlam]
                      · linarith only [h4, h5744, hlam]
                    · linarith only [h1, h5743, hlam]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4905, h4906, h5552, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4906, h5552, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h0, hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    rcases p5740_3 (m.d 0 1) (by simp) with h5752 | h5752
                    · rcases p5740_3 (m.d 0 2) (by simp) with h5753 | h5753
                      · rcases p5740_3 (m.d 0 3) (by simp) with h5754 | h5754
                        · linarith only [h4, h5754, hlam]
                        · rcases p5740_3 (m.d 0 4) (by simp) with h5756 | h5756
                          · linarith only [h5, h5756, hlam]
                          · linarith only [h5756, h7, hlam]
                      · linarith only [h4, h5753, hlam]
                    · linarith only [h1, h5752, hlam]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4905, h4906, h5552, h6, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h0, h4906, h5552, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h1, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h7, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4388, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h2, hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h5, hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    rcases p5740_3 (m.d 0 1) (by simp) with h5770 | h5770
                    · rcases p5740_3 (m.d 0 2) (by simp) with h5771 | h5771
                      · rcases p5740_3 (m.d 0 3) (by simp) with h5772 | h5772
                        · linarith only [h5772, h7, hlam]
                        · rcases p5740_3 (m.d 0 4) (by simp) with h5774 | h5774
                          · rcases p5740_3 (m.d 0 5) (by simp) with h5775 | h5775
                            · linarith only [h4905, h5775, hlam]
                            · linarith only [h4388, h5775, hlam]
                          · linarith only [h5774, h7, hlam]
                      · linarith only [h4, h5771, hlam]
                    · linarith only [h1, h5770, hlam]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4906, h5552, h6, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h3, hlam, p5740_0]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h6, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    rcases p5740_3 (m.d 0 1) (by simp) with h5785 | h5785
                    · rcases p5740_3 (m.d 0 2) (by simp) with h5786 | h5786
                      · rcases p5740_3 (m.d 0 3) (by simp) with h5787 | h5787
                        · linarith only [h4388, h5787, hlam]
                        · rcases p5740_3 (m.d 0 4) (by simp) with h5789 | h5789
                          · rcases p5740_3 (m.d 0 5) (by simp) with h5790 | h5790
                            · rcases h2bigk with h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c | h5791c
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                rcases p5791_3 (m.d 0 2) (by simp) with h5793 | h5793
                                · rcases p5791_3 (m.d 1 2) (by simp) with h5794 | h5794
                                  · linarith only [h0, h5794, hlam]
                                  · rcases p5791_3 (m.d 2 3) (by simp) with h5796 | h5796
                                    · linarith only [h4, h5796, hlam]
                                    · rcases p5791_3 (m.d 2 4) (by simp) with h5798 | h5798
                                      · linarith only [h5, h5798, hlam]
                                      · linarith only [h4907, h5798, hlam]
                                · linarith only [h0, h5793, hlam]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h4906, h5, h5552, h5738, hlam, p5791_2]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h4906, h5552, h5738, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, h4906, h5552, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, h5, h5552, h5738, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h4907, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h5552, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h4, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h4906, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h5734, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h5736, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h5, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, h4906, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                rcases p5791_3 (m.d 0 2) (by simp) with h5817 | h5817
                                · rcases p5791_3 (m.d 1 2) (by simp) with h5818 | h5818
                                  · linarith only [h4907, h5818, hlam]
                                  · linarith only [h4906, h5818, hlam]
                                · linarith only [h4, h5817, hlam]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, h4906, h5, h5552, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h6, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h0, h4906, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5791_1]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                rcases p5791_3 (m.d 0 2) (by simp) with h5826 | h5826
                                · rcases p5791_3 (m.d 1 2) (by simp) with h5827 | h5827
                                  · linarith only [h5552, h5827, hlam]
                                  · linarith only [h4906, h5827, hlam]
                                · linarith only [h4, h5826, hlam]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [h5738, hlam, p5791_0]
                              · have p5791_0 := h5791c.1
                                have p5791_1 := h5791c.2.1
                                have p5791_2 := h5791c.2.2.1
                                have p5791_3 := h5791c.2.2.2
                                linarith only [hlam, p5791_0]
                            · linarith only [h4388, h5790, hlam]
                          · linarith only [h5789, h7, hlam]
                      · linarith only [h4, h5786, hlam]
                    · linarith only [h1, h5785, hlam]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [h4905, hlam, p5740_1]
                  · have p5740_0 := h5740c.1
                    have p5740_1 := h5740c.2.1
                    have p5740_2 := h5740c.2.2.1
                    have p5740_3 := h5740c.2.2.2
                    linarith only [hlam, p5740_0]
                · linarith only [h4905, h5739, h7, hlam]
              · linarith only [h4907, h5733, h5738, hlam]
        · linarith only [h4905, h4906, h4907, h5733, h7, hc23, hc34, hlam, hphi]

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4906 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h4907 | h4907
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905 h4906 h4907
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905 h4906 h4907

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4906 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 4 (by decide) (by decide) with h5842 | h5842
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5843 | h5843
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5844 | h5844
      · linarith only [h4, h4906, h5842, h5844, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h4906, h5842, h5844, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5847 | h5847
      · linarith only [h4, h4906, h5842, h5847, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
      · linarith only [h4906, h5842, h5847, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5850 | h5850
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5851 | h5851
      · linarith only [h1, h5851, h7, hlam]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5853 | h5853
        · linarith only [h4, h4388, h4906, h5853, hlam]
        · linarith only [h4906, h5850, h5853, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5856 | h5856
      · linarith only [h1, h4, h4906, h5856, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5858 | h5858
        · linarith only [h1, h4, h4388, h4906, h5858, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5860 | h5860
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5861 | h5861
            · linarith only [h4, h5861, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5863 | h5863
              · linarith only [h4, h4388, h5863, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5865 | h5865
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5866 | h5866
                  · rcases h0bigk with h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c | h5867c
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4, h4906, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5870 | h5870
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5871 | h5871
                        · linarith only [h0, h5871, hlam]
                        · linarith only [h4, h5871, hlam]
                      · linarith only [h1, h5870, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5875 | h5875
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5876 | h5876
                        · linarith only [h0, h5876, hlam]
                        · linarith only [h5, h5876, hlam]
                      · linarith only [h2, h5875, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5880 | h5880
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5881 | h5881
                        · linarith only [h0, h5881, hlam]
                        · linarith only [h5881, h6, hlam]
                      · linarith only [h3, h5880, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h0, hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5887 | h5887
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5888 | h5888
                        · rcases p5867_3 (m.d 0 3) (by simp) with h5889 | h5889
                          · linarith only [h4, h5889, hlam]
                          · rcases p5867_3 (m.d 0 4) (by simp) with h5891 | h5891
                            · linarith only [h5, h5891, hlam]
                            · linarith only [h5891, h7, hlam]
                        · linarith only [h4, h5888, hlam]
                      · linarith only [h1, h5887, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5896 | h5896
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5897 | h5897
                        · rcases p5867_3 (m.d 0 3) (by simp) with h5898 | h5898
                          · linarith only [h4, h5898, hlam]
                          · rcases p5867_3 (m.d 0 4) (by simp) with h5900 | h5900
                            · linarith only [h5, h5900, hlam]
                            · rcases p5867_3 (m.d 0 5) (by simp) with h5902 | h5902
                              · linarith only [h5902, h6, hlam]
                              · rcases h2bigk with h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c | h5904c
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h4, h4388, h4905, h4906, hlam, p5867_1, p5904_2]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  rcases p5904_3 (m.d 0 2) (by simp) with h5907 | h5907
                                  · rcases p5904_3 (m.d 1 2) (by simp) with h5908 | h5908
                                    · linarith only [h0, h5908, hlam]
                                    · rcases p5904_3 (m.d 2 3) (by simp) with h5910 | h5910
                                      · linarith only [h5910, hlam, p5904_0]
                                      · rcases p5904_3 (m.d 2 4) (by simp) with h5912 | h5912
                                        · linarith only [h5, h5912, hlam]
                                        · linarith only [h5861, h5912, hlam]
                                  · linarith only [h5907, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  rcases p5904_3 (m.d 0 2) (by simp) with h5916 | h5916
                                  · rcases p5904_3 (m.d 1 2) (by simp) with h5917 | h5917
                                    · linarith only [h0, h5917, hlam]
                                    · rcases p5904_3 (m.d 2 3) (by simp) with h5919 | h5919
                                      · linarith only [h4, h5919, hlam]
                                      · rcases p5904_3 (m.d 2 4) (by simp) with h5921 | h5921
                                        · linarith only [h5921, hlam, p5904_0]
                                        · rcases p5904_3 (m.d 2 5) (by simp) with h5923 | h5923
                                          · linarith only [h5923, h6, hlam]
                                          · rcases h3bigk with h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c | h5925c
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4388, h4905, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5867_1, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h0, h4388, h4905, h4906, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h7, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4388, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h1, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4906, hlam, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h5856, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h5858, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h0, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h5861, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h5863, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hc03, hc34, hlam, hphi, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4906, hc12, hc34, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4906, hc12, hc34, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4, h4388, h4906, hc12, hc34, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4, h4906, hc12, hc35, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4906, hc12, hc35, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h4906, hc12, hc35, hlam, hphi, ht23, p5925_1]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [h5866, hlam, p5925_0]
                                            · have p5925_0 := h5925c.1
                                              have p5925_1 := h5925c.2.1
                                              have p5925_2 := h5925c.2.2.1
                                              have p5925_3 := h5925c.2.2.2
                                              linarith only [hlam, p5925_0]
                                  · linarith only [h5916, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  rcases p5904_3 (m.d 0 2) (by simp) with h5952 | h5952
                                  · rcases p5904_3 (m.d 1 2) (by simp) with h5953 | h5953
                                    · linarith only [h0, h5953, hlam]
                                    · rcases p5904_3 (m.d 2 3) (by simp) with h5955 | h5955
                                      · linarith only [h4, h5955, hlam]
                                      · rcases p5904_3 (m.d 2 4) (by simp) with h5957 | h5957
                                        · linarith only [h5, h5957, hlam]
                                        · linarith only [h5865, h5957, hlam]
                                  · linarith only [h5952, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h4906, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5842, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5850, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h4, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h5, h5863, h5865, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5861, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5863, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h5, hc01, hc25, hlam, hphi, ht0b, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h6, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h4905, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h0, h4905, h4906, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5867_1, p5904_1]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [h5865, hlam, p5904_0]
                                · have p5904_0 := h5904c.1
                                  have p5904_1 := h5904c.2.1
                                  have p5904_2 := h5904c.2.2.1
                                  have p5904_3 := h5904c.2.2.2
                                  linarith only [hlam, p5904_0]
                        · linarith only [h5, h5897, hlam]
                      · linarith only [h2, h5896, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      rcases p5867_3 (m.d 0 1) (by simp) with h5983 | h5983
                      · rcases p5867_3 (m.d 0 2) (by simp) with h5984 | h5984
                        · rcases p5867_3 (m.d 0 3) (by simp) with h5985 | h5985
                          · linarith only [h4, h5985, hlam]
                          · rcases p5867_3 (m.d 0 4) (by simp) with h5987 | h5987
                            · linarith only [h5, h5987, hlam]
                            · linarith only [h4905, h5987, hlam]
                        · linarith only [h5984, h6, hlam]
                      · linarith only [h3, h5983, hlam]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h1, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h7, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4388, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h2, hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h5, hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4, h4906, h7, hc12, hc34, hlam, hphi, ht23, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4, h4388, h4906, h7, hc12, hc34, hlam, hphi, ht23, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h3, hlam, p5867_0]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h6, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4, h4388, h4906, h5866, hc12, hc34, hlam, hphi, ht23, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [h4905, hlam, p5867_1]
                    · have p5867_0 := h5867c.1
                      have p5867_1 := h5867c.2.1
                      have p5867_2 := h5867c.2.2.1
                      have p5867_3 := h5867c.2.2.2
                      linarith only [hlam, p5867_0]
                  · linarith only [h2, h5860, h5866, h7, hlam]
                · linarith only [h5842, h5860, h5865, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6009 | h6009
            · linarith only [h4, h6009, h7, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6011 | h6011
              · linarith only [h4, h4388, h6011, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6013 | h6013
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6014 | h6014
                  · rcases h0bigk with h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c | h6015c
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4906, h5, h5856, h5860, h6013, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      rcases p6015_3 (m.d 0 1) (by simp) with h6018 | h6018
                      · rcases p6015_3 (m.d 0 2) (by simp) with h6019 | h6019
                        · linarith only [h0, h6019, hlam]
                        · linarith only [h4, h6019, hlam]
                      · linarith only [h1, h6018, hlam]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4906, h5, h5856, h5860, h6013, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      rcases p6015_3 (m.d 0 1) (by simp) with h6024 | h6024
                      · rcases p6015_3 (m.d 0 2) (by simp) with h6025 | h6025
                        · linarith only [h0, h6025, hlam]
                        · linarith only [h6, h6025, hlam]
                      · linarith only [h3, h6024, hlam]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h0, hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      rcases p6015_3 (m.d 0 1) (by simp) with h6031 | h6031
                      · rcases p6015_3 (m.d 0 2) (by simp) with h6032 | h6032
                        · rcases p6015_3 (m.d 0 3) (by simp) with h6033 | h6033
                          · linarith only [h4, h6033, hlam]
                          · rcases p6015_3 (m.d 0 4) (by simp) with h6035 | h6035
                            · linarith only [h5, h6035, hlam]
                            · linarith only [h6035, h7, hlam]
                        · linarith only [h4, h6032, hlam]
                      · linarith only [h1, h6031, hlam]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4906, h5, h5856, h5860, h6013, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      rcases p6015_3 (m.d 0 1) (by simp) with h6041 | h6041
                      · rcases p6015_3 (m.d 0 2) (by simp) with h6042 | h6042
                        · rcases p6015_3 (m.d 0 3) (by simp) with h6043 | h6043
                          · linarith only [h4, h6043, hlam]
                          · rcases p6015_3 (m.d 0 4) (by simp) with h6045 | h6045
                            · linarith only [h5, h6045, hlam]
                            · linarith only [h4905, h6045, hlam]
                        · linarith only [h6, h6042, hlam]
                      · linarith only [h3, h6041, hlam]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h1, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h7, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4388, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h2, hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h5, hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4, h4906, h7, hc12, hc34, hlam, hphi, ht23, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4905, h4906, h5856, h5860, h7, hc12, hc34, hlam, hphi, ht23, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h3, hlam, p6015_0]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h6, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4, h4388, h4906, h6014, hc12, hc34, hlam, hphi, ht23, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [h4905, hlam, p6015_1]
                    · have p6015_0 := h6015c.1
                      have p6015_1 := h6015c.2.1
                      have p6015_2 := h6015c.2.2.1
                      have p6015_3 := h6015c.2.2.2
                      linarith only [hlam, p6015_0]
                  · linarith only [h4, h4906, h6014, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h4905, h5842, h6013, h7, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 13644000 in
set_option maxHeartbeats 13644000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4388 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4905 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h4906 | h4906
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905 h4906
  · exact r1l7_10_12_23_L_I_L_I_H_I_s6_x1_x1_x0_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h4388 h4905 h4906

end R2N4
