import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
    (h4718 : (m.d 4 5 + m.lam ≤ m.d 2 4 ∧ m.d 4 5 < m.d 2 5 ∧ m.d 2 5 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 3 4 5 (by decide) (by decide) with h5599 | h5599
  · linarith only [h0, h3576, h4, h4718, h5599, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
  · rcases h1bigk with h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h0, h3576, h4, h4718, h7, h9, hlam, p5601_2]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h5604 | h5604
      · rcases p5601_3 (m.d 1 2) (by simp) with h5605 | h5605
        · linarith only [h0, h5605, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h5607 | h5607
          · linarith only [h5607, hlam, p5601_0]
          · rcases p5601_3 (m.d 1 4) (by simp) with h5609 | h5609
            · linarith only [h2, h5609, hlam]
            · rcases p5601_3 (m.d 1 5) (by simp) with h5611 | h5611
              · linarith only [h3, h5611, hlam]
              · rcases h1emax with h5613 | h5613 | h5613 | h5613 | h5613
                · linarith only [h0, h3576, h4, h4718, h5613, h7, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases h2bigk with h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c | h5615c
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h3576, h4, h4718, h7, h9, hlam, p5615_2]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    rcases p5615_3 (m.d 0 2) (by simp) with h5618 | h5618
                    · rcases p5615_3 (m.d 1 2) (by simp) with h5619 | h5619
                      · linarith only [h0, h5619, hlam]
                      · rcases p5615_3 (m.d 2 3) (by simp) with h5621 | h5621
                        · linarith only [h5621, hlam, p5615_0]
                        · rcases p5615_3 (m.d 2 4) (by simp) with h5623 | h5623
                          · linarith only [h5, h5623, hlam]
                          · rcases p5615_3 (m.d 2 5) (by simp) with h5625 | h5625
                            · linarith only [h5625, h6, hlam]
                            · rcases h4bigk with h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c | h5627c
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                rcases p5627_3 (m.d 0 4) (by simp) with h5629 | h5629
                                · rcases p5627_3 (m.d 1 4) (by simp) with h5630 | h5630
                                  · linarith only [h2, h5630, hlam]
                                  · rcases p5627_3 (m.d 2 4) (by simp) with h5632 | h5632
                                    · linarith only [h5, h5632, hlam]
                                    · linarith only [h3576, h5632, hlam]
                                · linarith only [h2, h5629, hlam]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                rcases p5627_3 (m.d 0 4) (by simp) with h5636 | h5636
                                · rcases p5627_3 (m.d 1 4) (by simp) with h5637 | h5637
                                  · linarith only [h2, h5637, hlam]
                                  · rcases p5627_3 (m.d 2 4) (by simp) with h5639 | h5639
                                    · linarith only [h5, h5639, hlam]
                                    · rcases p5627_3 (m.d 3 4) (by simp) with h5641 | h5641
                                      · linarith only [h5641, h7, hlam]
                                      · rcases p5627_3 (m.d 4 5) (by simp) with h5643 | h5643
                                        · linarith only [h5643, h9, hlam]
                                        · linarith only [h4718, h5643, hlam]
                                · linarith only [h5, h5636, hlam]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                rcases p5627_3 (m.d 0 4) (by simp) with h5647 | h5647
                                · rcases p5627_3 (m.d 1 4) (by simp) with h5648 | h5648
                                  · linarith only [h2, h5648, hlam]
                                  · linarith only [h4129, h5648, hlam]
                                · linarith only [h5647, h7, hlam]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h3576, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h2, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h3576, hlam, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h3576, h4718, hc34, hc45, hlam, hphi, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h4131, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h5, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h4718, hc14, hc45, hlam, hphi, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h0, h4, h4718, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h4718, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h7, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h4129, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h4716, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h5599, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h9, hlam, p5627_0]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                rcases p5627_3 (m.d 0 4) (by simp) with h5669 | h5669
                                · rcases p5627_3 (m.d 1 4) (by simp) with h5670 | h5670
                                  · linarith only [h5670, hlam, p5627_0]
                                  · rcases p5627_3 (m.d 2 4) (by simp) with h5672 | h5672
                                    · linarith only [h4718, h5672, hlam]
                                    · linarith only [h3576, h5672, hlam]
                                · linarith only [h2, h5669, hlam]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5627_1]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                rcases p5627_3 (m.d 0 4) (by simp) with h5677 | h5677
                                · rcases p5627_3 (m.d 1 4) (by simp) with h5678 | h5678
                                  · linarith only [h4131, h5678, hlam]
                                  · linarith only [h4129, h5678, hlam]
                                · linarith only [h5677, h7, hlam]
                              · have p5627_0 := h5627c.1
                                have p5627_1 := h5627c.2.1
                                have p5627_2 := h5627c.2.2.1
                                have p5627_3 := h5627c.2.2.2
                                linarith only [hlam, p5627_0]
                    · linarith only [h5618, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    rcases p5615_3 (m.d 0 2) (by simp) with h5684 | h5684
                    · rcases p5615_3 (m.d 1 2) (by simp) with h5685 | h5685
                      · linarith only [h0, h5685, hlam]
                      · rcases p5615_3 (m.d 2 3) (by simp) with h5687 | h5687
                        · linarith only [h4, h5687, hlam]
                        · linarith only [h4716, h5687, hlam]
                    · linarith only [h5684, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    rcases p5615_3 (m.d 0 2) (by simp) with h5691 | h5691
                    · rcases p5615_3 (m.d 1 2) (by simp) with h5692 | h5692
                      · linarith only [h0, h5692, hlam]
                      · rcases p5615_3 (m.d 2 3) (by simp) with h5694 | h5694
                        · linarith only [h4, h5694, hlam]
                        · linarith only [h4717, h5694, hlam]
                    · linarith only [h5691, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h0, hlam, p5615_1]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h10, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h3576, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h4058, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h4, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    rcases p5615_3 (m.d 0 2) (by simp) with h5704 | h5704
                    · rcases p5615_3 (m.d 1 2) (by simp) with h5705 | h5705
                      · linarith only [h5705, hlam, p5615_0]
                      · rcases p5615_3 (m.d 2 3) (by simp) with h5707 | h5707
                        · rcases p5615_3 (m.d 2 4) (by simp) with h5708 | h5708
                          · linarith only [h4716, h5708, hlam]
                          · linarith only [h3576, h5708, hlam]
                        · linarith only [h5707, hlam, p5615_0]
                    · linarith only [h0, h5704, hlam]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p5615_1]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5615_1]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h5, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5615_1]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h4716, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h4718, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h6, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    rcases p5615_3 (m.d 0 2) (by simp) with h5722 | h5722
                    · rcases p5615_3 (m.d 1 2) (by simp) with h5723 | h5723
                      · linarith only [h5723, hlam, p5615_0]
                      · rcases p5615_3 (m.d 2 3) (by simp) with h5725 | h5725
                        · rcases p5615_3 (m.d 2 4) (by simp) with h5726 | h5726
                          · linarith only [h4718, h5726, hlam]
                          · linarith only [h3576, h5726, hlam]
                        · linarith only [h10, h5725, hlam]
                    · linarith only [h0, h5722, hlam]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h4717, hlam, p5615_0]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [h0, h3576, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5615_1]
                  · have p5615_0 := h5615c.1
                    have p5615_1 := h5615c.2.1
                    have p5615_2 := h5615c.2.2.1
                    have p5615_3 := h5615c.2.2.2
                    linarith only [hlam, p5615_0]
                · rcases h2bigk with h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c | h5734c
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h3576, h4, h4718, h7, h9, hlam, p5734_2]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    rcases p5734_3 (m.d 0 2) (by simp) with h5737 | h5737
                    · rcases p5734_3 (m.d 1 2) (by simp) with h5738 | h5738
                      · linarith only [h0, h5738, hlam]
                      · rcases p5734_3 (m.d 2 3) (by simp) with h5740 | h5740
                        · linarith only [h5740, hlam, p5734_0]
                        · rcases p5734_3 (m.d 2 4) (by simp) with h5742 | h5742
                          · linarith only [h5, h5742, hlam]
                          · rcases p5734_3 (m.d 2 5) (by simp) with h5744 | h5744
                            · linarith only [h5744, h6, hlam]
                            · rcases h4bigk with h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c | h5746c
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                rcases p5746_3 (m.d 0 4) (by simp) with h5748 | h5748
                                · rcases p5746_3 (m.d 1 4) (by simp) with h5749 | h5749
                                  · linarith only [h2, h5749, hlam]
                                  · rcases p5746_3 (m.d 2 4) (by simp) with h5751 | h5751
                                    · linarith only [h5, h5751, hlam]
                                    · linarith only [h3576, h5751, hlam]
                                · linarith only [h2, h5748, hlam]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                rcases p5746_3 (m.d 0 4) (by simp) with h5755 | h5755
                                · rcases p5746_3 (m.d 1 4) (by simp) with h5756 | h5756
                                  · linarith only [h2, h5756, hlam]
                                  · rcases p5746_3 (m.d 2 4) (by simp) with h5758 | h5758
                                    · linarith only [h5, h5758, hlam]
                                    · rcases p5746_3 (m.d 3 4) (by simp) with h5760 | h5760
                                      · linarith only [h5760, h7, hlam]
                                      · rcases p5746_3 (m.d 4 5) (by simp) with h5762 | h5762
                                        · linarith only [h5762, h9, hlam]
                                        · linarith only [h4718, h5762, hlam]
                                · linarith only [h5, h5755, hlam]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                rcases p5746_3 (m.d 0 4) (by simp) with h5766 | h5766
                                · rcases p5746_3 (m.d 1 4) (by simp) with h5767 | h5767
                                  · linarith only [h2, h5767, hlam]
                                  · linarith only [h4129, h5767, hlam]
                                · linarith only [h5766, h7, hlam]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h3576, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h2, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h3576, hlam, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h3576, h4718, hc34, hc45, hlam, hphi, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h4131, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h5, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h4718, hc14, hc45, hlam, hphi, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h0, h4, h4718, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h4718, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h7, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h4129, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h4716, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h5599, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h9, hlam, p5746_0]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                rcases p5746_3 (m.d 0 4) (by simp) with h5788 | h5788
                                · rcases p5746_3 (m.d 1 4) (by simp) with h5789 | h5789
                                  · linarith only [h5789, hlam, p5746_0]
                                  · rcases p5746_3 (m.d 2 4) (by simp) with h5791 | h5791
                                    · linarith only [h4718, h5791, hlam]
                                    · linarith only [h3576, h5791, hlam]
                                · linarith only [h2, h5788, hlam]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5746_1]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                rcases p5746_3 (m.d 0 4) (by simp) with h5796 | h5796
                                · rcases p5746_3 (m.d 1 4) (by simp) with h5797 | h5797
                                  · linarith only [h4131, h5797, hlam]
                                  · linarith only [h4129, h5797, hlam]
                                · linarith only [h5796, h7, hlam]
                              · have p5746_0 := h5746c.1
                                have p5746_1 := h5746c.2.1
                                have p5746_2 := h5746c.2.2.1
                                have p5746_3 := h5746c.2.2.2
                                linarith only [hlam, p5746_0]
                    · linarith only [h5737, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    rcases p5734_3 (m.d 0 2) (by simp) with h5803 | h5803
                    · rcases p5734_3 (m.d 1 2) (by simp) with h5804 | h5804
                      · linarith only [h0, h5804, hlam]
                      · rcases p5734_3 (m.d 2 3) (by simp) with h5806 | h5806
                        · linarith only [h4, h5806, hlam]
                        · linarith only [h4716, h5806, hlam]
                    · linarith only [h5803, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    rcases p5734_3 (m.d 0 2) (by simp) with h5810 | h5810
                    · rcases p5734_3 (m.d 1 2) (by simp) with h5811 | h5811
                      · linarith only [h0, h5811, hlam]
                      · rcases p5734_3 (m.d 2 3) (by simp) with h5813 | h5813
                        · linarith only [h4, h5813, hlam]
                        · linarith only [h4717, h5813, hlam]
                    · linarith only [h5810, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h0, hlam, p5734_1]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h10, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h3576, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h4058, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h4, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    rcases p5734_3 (m.d 0 2) (by simp) with h5823 | h5823
                    · rcases p5734_3 (m.d 1 2) (by simp) with h5824 | h5824
                      · linarith only [h5824, hlam, p5734_0]
                      · rcases p5734_3 (m.d 2 3) (by simp) with h5826 | h5826
                        · rcases p5734_3 (m.d 2 4) (by simp) with h5827 | h5827
                          · linarith only [h4716, h5827, hlam]
                          · linarith only [h3576, h5827, hlam]
                        · linarith only [h5826, hlam, p5734_0]
                    · linarith only [h0, h5823, hlam]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p5734_1]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5734_1]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h5, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5734_1]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h4716, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h4718, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h6, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    rcases p5734_3 (m.d 0 2) (by simp) with h5841 | h5841
                    · rcases p5734_3 (m.d 1 2) (by simp) with h5842 | h5842
                      · linarith only [h5842, hlam, p5734_0]
                      · rcases p5734_3 (m.d 2 3) (by simp) with h5844 | h5844
                        · rcases p5734_3 (m.d 2 4) (by simp) with h5845 | h5845
                          · linarith only [h4718, h5845, hlam]
                          · linarith only [h3576, h5845, hlam]
                        · linarith only [h10, h5844, hlam]
                    · linarith only [h0, h5841, hlam]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h4717, hlam, p5734_0]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [h3576, hc12, hc25, hlam, hphi, p5734_1]
                  · have p5734_0 := h5734c.1
                    have p5734_1 := h5734c.2.1
                    have p5734_2 := h5734c.2.2.1
                    have p5734_3 := h5734c.2.2.2
                    linarith only [hlam, p5734_0]
                · rcases h2bigk with h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c | h5853c
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h3576, h4, h4718, h7, h9, hlam, p5853_2]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    rcases p5853_3 (m.d 0 2) (by simp) with h5856 | h5856
                    · rcases p5853_3 (m.d 1 2) (by simp) with h5857 | h5857
                      · linarith only [h0, h5857, hlam]
                      · rcases p5853_3 (m.d 2 3) (by simp) with h5859 | h5859
                        · linarith only [h5859, hlam, p5853_0]
                        · rcases p5853_3 (m.d 2 4) (by simp) with h5861 | h5861
                          · linarith only [h5, h5861, hlam]
                          · rcases p5853_3 (m.d 2 5) (by simp) with h5863 | h5863
                            · linarith only [h5863, h6, hlam]
                            · rcases h4bigk with h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c | h5865c
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                rcases p5865_3 (m.d 0 4) (by simp) with h5867 | h5867
                                · rcases p5865_3 (m.d 1 4) (by simp) with h5868 | h5868
                                  · linarith only [h2, h5868, hlam]
                                  · rcases p5865_3 (m.d 2 4) (by simp) with h5870 | h5870
                                    · linarith only [h5, h5870, hlam]
                                    · linarith only [h3576, h5870, hlam]
                                · linarith only [h2, h5867, hlam]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                rcases p5865_3 (m.d 0 4) (by simp) with h5874 | h5874
                                · rcases p5865_3 (m.d 1 4) (by simp) with h5875 | h5875
                                  · linarith only [h2, h5875, hlam]
                                  · rcases p5865_3 (m.d 2 4) (by simp) with h5877 | h5877
                                    · linarith only [h5, h5877, hlam]
                                    · rcases p5865_3 (m.d 3 4) (by simp) with h5879 | h5879
                                      · linarith only [h5879, h7, hlam]
                                      · rcases p5865_3 (m.d 4 5) (by simp) with h5881 | h5881
                                        · linarith only [h5881, h9, hlam]
                                        · linarith only [h4718, h5881, hlam]
                                · linarith only [h5, h5874, hlam]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                rcases p5865_3 (m.d 0 4) (by simp) with h5885 | h5885
                                · rcases p5865_3 (m.d 1 4) (by simp) with h5886 | h5886
                                  · linarith only [h2, h5886, hlam]
                                  · linarith only [h4129, h5886, hlam]
                                · linarith only [h5885, h7, hlam]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h3576, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h2, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h3576, hlam, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h3576, h4718, hc34, hc45, hlam, hphi, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h4131, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h5, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h4718, hc14, hc45, hlam, hphi, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h0, h4716, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5853_1, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h4718, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h7, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h4129, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h4716, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h5599, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h9, hlam, p5865_0]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                rcases p5865_3 (m.d 0 4) (by simp) with h5907 | h5907
                                · rcases p5865_3 (m.d 1 4) (by simp) with h5908 | h5908
                                  · linarith only [h5908, hlam, p5865_0]
                                  · rcases p5865_3 (m.d 2 4) (by simp) with h5910 | h5910
                                    · linarith only [h4718, h5910, hlam]
                                    · linarith only [h3576, h5910, hlam]
                                · linarith only [h2, h5907, hlam]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5865_1]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                rcases p5865_3 (m.d 0 4) (by simp) with h5915 | h5915
                                · rcases p5865_3 (m.d 1 4) (by simp) with h5916 | h5916
                                  · linarith only [h4131, h5916, hlam]
                                  · linarith only [h4129, h5916, hlam]
                                · linarith only [h5915, h7, hlam]
                              · have p5865_0 := h5865c.1
                                have p5865_1 := h5865c.2.1
                                have p5865_2 := h5865c.2.2.1
                                have p5865_3 := h5865c.2.2.2
                                linarith only [hlam, p5865_0]
                    · linarith only [h5856, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    rcases p5853_3 (m.d 0 2) (by simp) with h5922 | h5922
                    · rcases p5853_3 (m.d 1 2) (by simp) with h5923 | h5923
                      · linarith only [h0, h5923, hlam]
                      · rcases p5853_3 (m.d 2 3) (by simp) with h5925 | h5925
                        · linarith only [h4, h5925, hlam]
                        · linarith only [h4716, h5925, hlam]
                    · linarith only [h5922, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    rcases p5853_3 (m.d 0 2) (by simp) with h5929 | h5929
                    · rcases p5853_3 (m.d 1 2) (by simp) with h5930 | h5930
                      · linarith only [h0, h5930, hlam]
                      · rcases p5853_3 (m.d 2 3) (by simp) with h5932 | h5932
                        · linarith only [h4, h5932, hlam]
                        · linarith only [h4717, h5932, hlam]
                    · linarith only [h5929, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h0, hlam, p5853_1]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h10, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h3576, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h4058, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h4, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    rcases p5853_3 (m.d 0 2) (by simp) with h5942 | h5942
                    · rcases p5853_3 (m.d 1 2) (by simp) with h5943 | h5943
                      · linarith only [h5943, hlam, p5853_0]
                      · rcases p5853_3 (m.d 2 3) (by simp) with h5945 | h5945
                        · rcases p5853_3 (m.d 2 4) (by simp) with h5946 | h5946
                          · linarith only [h4716, h5946, hlam]
                          · linarith only [h3576, h5946, hlam]
                        · linarith only [h5945, hlam, p5853_0]
                    · linarith only [h0, h5942, hlam]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p5853_1]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5853_1]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h5, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5853_1]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h4716, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h4718, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h6, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    rcases p5853_3 (m.d 0 2) (by simp) with h5960 | h5960
                    · rcases p5853_3 (m.d 1 2) (by simp) with h5961 | h5961
                      · linarith only [h5961, hlam, p5853_0]
                      · rcases p5853_3 (m.d 2 3) (by simp) with h5963 | h5963
                        · rcases p5853_3 (m.d 2 4) (by simp) with h5964 | h5964
                          · linarith only [h4718, h5964, hlam]
                          · linarith only [h3576, h5964, hlam]
                        · linarith only [h10, h5963, hlam]
                    · linarith only [h0, h5960, hlam]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h4717, hlam, p5853_0]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [h0, h3576, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5853_1]
                  · have p5853_0 := h5853c.1
                    have p5853_1 := h5853c.2.1
                    have p5853_2 := h5853c.2.2.1
                    have p5853_3 := h5853c.2.2.2
                    linarith only [hlam, p5853_0]
                · rcases h2bigk with h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c | h5972c
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h3576, h4, h4718, h7, h9, hlam, p5972_2]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    rcases p5972_3 (m.d 0 2) (by simp) with h5975 | h5975
                    · rcases p5972_3 (m.d 1 2) (by simp) with h5976 | h5976
                      · linarith only [h0, h5976, hlam]
                      · rcases p5972_3 (m.d 2 3) (by simp) with h5978 | h5978
                        · linarith only [h5978, hlam, p5972_0]
                        · rcases p5972_3 (m.d 2 4) (by simp) with h5980 | h5980
                          · linarith only [h5, h5980, hlam]
                          · rcases p5972_3 (m.d 2 5) (by simp) with h5982 | h5982
                            · linarith only [h5982, h6, hlam]
                            · rcases h4bigk with h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c | h5984c
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                rcases p5984_3 (m.d 0 4) (by simp) with h5986 | h5986
                                · rcases p5984_3 (m.d 1 4) (by simp) with h5987 | h5987
                                  · linarith only [h2, h5987, hlam]
                                  · rcases p5984_3 (m.d 2 4) (by simp) with h5989 | h5989
                                    · linarith only [h5, h5989, hlam]
                                    · linarith only [h3576, h5989, hlam]
                                · linarith only [h2, h5986, hlam]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                rcases p5984_3 (m.d 0 4) (by simp) with h5993 | h5993
                                · rcases p5984_3 (m.d 1 4) (by simp) with h5994 | h5994
                                  · linarith only [h2, h5994, hlam]
                                  · rcases p5984_3 (m.d 2 4) (by simp) with h5996 | h5996
                                    · linarith only [h5, h5996, hlam]
                                    · rcases p5984_3 (m.d 3 4) (by simp) with h5998 | h5998
                                      · linarith only [h5998, h7, hlam]
                                      · rcases p5984_3 (m.d 4 5) (by simp) with h6000 | h6000
                                        · linarith only [h6000, h9, hlam]
                                        · linarith only [h4718, h6000, hlam]
                                · linarith only [h5, h5993, hlam]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                rcases p5984_3 (m.d 0 4) (by simp) with h6004 | h6004
                                · rcases p5984_3 (m.d 1 4) (by simp) with h6005 | h6005
                                  · linarith only [h2, h6005, hlam]
                                  · linarith only [h4129, h6005, hlam]
                                · linarith only [h6004, h7, hlam]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h3576, h4718, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h2, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h3576, hlam, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h3576, h4718, hc34, hc45, hlam, hphi, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h4131, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h5, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h4718, hc14, hc45, hlam, hphi, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h0, h4, h4718, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h4718, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h7, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h4129, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h4716, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h5599, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h9, hlam, p5984_0]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                rcases p5984_3 (m.d 0 4) (by simp) with h6026 | h6026
                                · rcases p5984_3 (m.d 1 4) (by simp) with h6027 | h6027
                                  · linarith only [h6027, hlam, p5984_0]
                                  · rcases p5984_3 (m.d 2 4) (by simp) with h6029 | h6029
                                    · linarith only [h4718, h6029, hlam]
                                    · linarith only [h3576, h6029, hlam]
                                · linarith only [h2, h6026, hlam]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [h0, h3576, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5984_1]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                rcases p5984_3 (m.d 0 4) (by simp) with h6034 | h6034
                                · rcases p5984_3 (m.d 1 4) (by simp) with h6035 | h6035
                                  · linarith only [h4131, h6035, hlam]
                                  · linarith only [h4129, h6035, hlam]
                                · linarith only [h6034, h7, hlam]
                              · have p5984_0 := h5984c.1
                                have p5984_1 := h5984c.2.1
                                have p5984_2 := h5984c.2.2.1
                                have p5984_3 := h5984c.2.2.2
                                linarith only [hlam, p5984_0]
                    · linarith only [h5975, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    rcases p5972_3 (m.d 0 2) (by simp) with h6041 | h6041
                    · rcases p5972_3 (m.d 1 2) (by simp) with h6042 | h6042
                      · linarith only [h0, h6042, hlam]
                      · rcases p5972_3 (m.d 2 3) (by simp) with h6044 | h6044
                        · linarith only [h4, h6044, hlam]
                        · linarith only [h4716, h6044, hlam]
                    · linarith only [h6041, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    rcases p5972_3 (m.d 0 2) (by simp) with h6048 | h6048
                    · rcases p5972_3 (m.d 1 2) (by simp) with h6049 | h6049
                      · linarith only [h0, h6049, hlam]
                      · rcases p5972_3 (m.d 2 3) (by simp) with h6051 | h6051
                        · linarith only [h4, h6051, hlam]
                        · linarith only [h4717, h6051, hlam]
                    · linarith only [h6048, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h0, hlam, p5972_1]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h10, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h3576, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h4058, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h4, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    rcases p5972_3 (m.d 0 2) (by simp) with h6061 | h6061
                    · rcases p5972_3 (m.d 1 2) (by simp) with h6062 | h6062
                      · linarith only [h6062, hlam, p5972_0]
                      · rcases p5972_3 (m.d 2 3) (by simp) with h6064 | h6064
                        · rcases p5972_3 (m.d 2 4) (by simp) with h6065 | h6065
                          · linarith only [h4716, h6065, hlam]
                          · linarith only [h3576, h6065, hlam]
                        · linarith only [h6064, hlam, p5972_0]
                    · linarith only [h0, h6061, hlam]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p5972_1]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5972_1]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h5, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5972_1]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h4716, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h4718, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h6, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    rcases p5972_3 (m.d 0 2) (by simp) with h6079 | h6079
                    · rcases p5972_3 (m.d 1 2) (by simp) with h6080 | h6080
                      · linarith only [h6080, hlam, p5972_0]
                      · rcases p5972_3 (m.d 2 3) (by simp) with h6082 | h6082
                        · rcases p5972_3 (m.d 2 4) (by simp) with h6083 | h6083
                          · linarith only [h4718, h6083, hlam]
                          · linarith only [h3576, h6083, hlam]
                        · linarith only [h10, h6082, hlam]
                    · linarith only [h0, h6079, hlam]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h4717, hlam, p5972_0]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [h0, h3576, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5972_1]
                  · have p5972_0 := h5972c.1
                    have p5972_1 := h5972c.2.1
                    have p5972_2 := h5972c.2.2.1
                    have p5972_3 := h5972c.2.2.2
                    linarith only [hlam, p5972_0]
      · linarith only [h5604, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6092 | h6092
      · rcases p5601_3 (m.d 1 2) (by simp) with h6093 | h6093
        · linarith only [h0, h6093, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6095 | h6095
          · linarith only [h1, h6095, hlam]
          · linarith only [h4129, h6095, hlam]
      · linarith only [h6092, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6099 | h6099
      · rcases p5601_3 (m.d 1 2) (by simp) with h6100 | h6100
        · linarith only [h0, h6100, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6102 | h6102
          · linarith only [h1, h6102, hlam]
          · linarith only [h4130, h6102, hlam]
      · linarith only [h6099, hlam, p5601_0]
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
      linarith only [h10, hlam, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h3576, hlam, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h4058, hlam, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h1, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6112 | h6112
      · rcases p5601_3 (m.d 1 2) (by simp) with h6113 | h6113
        · linarith only [h10, h6113, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6115 | h6115
          · rcases p5601_3 (m.d 1 4) (by simp) with h6116 | h6116
            · linarith only [h4129, h6116, hlam]
            · linarith only [h3576, h6116, hlam]
          · linarith only [h10, h6115, hlam]
      · linarith only [h0, h6112, hlam]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6122 | h6122
      · rcases p5601_3 (m.d 1 2) (by simp) with h6123 | h6123
        · linarith only [h10, h6123, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6125 | h6125
          · rcases p5601_3 (m.d 1 4) (by simp) with h6126 | h6126
            · linarith only [h4129, h6126, hlam]
            · rcases p5601_3 (m.d 1 5) (by simp) with h6128 | h6128
              · linarith only [h4130, h6128, hlam]
              · linarith only [h4131, h6128, hlam]
          · linarith only [h4129, h6125, hlam]
      · linarith only [h2, h6122, hlam]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6133 | h6133
      · rcases p5601_3 (m.d 1 2) (by simp) with h6134 | h6134
        · linarith only [h10, h6134, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6136 | h6136
          · rcases p5601_3 (m.d 1 4) (by simp) with h6137 | h6137
            · linarith only [h4129, h6137, hlam]
            · rcases p5601_3 (m.d 1 5) (by simp) with h6139 | h6139
              · linarith only [h4130, h6139, hlam]
              · rcases h1emax with h6141 | h6141 | h6141 | h6141 | h6141
                · linarith only [h1, h3576, h4131, h6141, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5601_1]
                · rcases h2bigk with h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c | h6143c
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h10, h3576, h4, h4131, hlam, p5601_1, p6143_2]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h0, h10, h3576, h4131, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    rcases p6143_3 (m.d 0 2) (by simp) with h6147 | h6147
                    · rcases p6143_3 (m.d 1 2) (by simp) with h6148 | h6148
                      · linarith only [h0, h6148, hlam]
                      · rcases p6143_3 (m.d 2 3) (by simp) with h6150 | h6150
                        · linarith only [h4, h6150, hlam]
                        · linarith only [h4716, h6150, hlam]
                    · linarith only [h6147, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    rcases p6143_3 (m.d 0 2) (by simp) with h6154 | h6154
                    · rcases p6143_3 (m.d 1 2) (by simp) with h6155 | h6155
                      · linarith only [h0, h6155, hlam]
                      · rcases p6143_3 (m.d 2 3) (by simp) with h6157 | h6157
                        · linarith only [h4, h6157, hlam]
                        · linarith only [h4717, h6157, hlam]
                    · linarith only [h6154, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h0, hlam, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h10, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h3576, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h4058, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h4, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    rcases p6143_3 (m.d 0 2) (by simp) with h6167 | h6167
                    · rcases p6143_3 (m.d 1 2) (by simp) with h6168 | h6168
                      · linarith only [h6168, hlam, p6143_0]
                      · rcases p6143_3 (m.d 2 3) (by simp) with h6170 | h6170
                        · rcases p6143_3 (m.d 2 4) (by simp) with h6171 | h6171
                          · linarith only [h4716, h6171, hlam]
                          · linarith only [h3576, h6171, hlam]
                        · linarith only [h6170, hlam, p6143_0]
                    · linarith only [h0, h6167, hlam]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h5, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h4716, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h4718, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h6, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    rcases p6143_3 (m.d 0 2) (by simp) with h6185 | h6185
                    · rcases p6143_3 (m.d 1 2) (by simp) with h6186 | h6186
                      · linarith only [h6186, hlam, p6143_0]
                      · rcases p6143_3 (m.d 2 3) (by simp) with h6188 | h6188
                        · rcases p6143_3 (m.d 2 4) (by simp) with h6189 | h6189
                          · linarith only [h4718, h6189, hlam]
                          · linarith only [h3576, h6189, hlam]
                        · linarith only [h10, h6188, hlam]
                    · linarith only [h0, h6185, hlam]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h4717, hlam, p6143_0]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [h0, h3576, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6143_1]
                  · have p6143_0 := h6143c.1
                    have p6143_1 := h6143c.2.1
                    have p6143_2 := h6143c.2.2.1
                    have p6143_3 := h6143c.2.2.2
                    linarith only [hlam, p6143_0]
                · linarith only [h3576, h4131, h6141, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5601_1]
                · rcases h2bigk with h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c | h6198c
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h10, h3576, h4, h4131, hlam, p5601_1, p6198_2]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h10, h3576, h4131, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    rcases p6198_3 (m.d 0 2) (by simp) with h6202 | h6202
                    · rcases p6198_3 (m.d 1 2) (by simp) with h6203 | h6203
                      · linarith only [h0, h6203, hlam]
                      · rcases p6198_3 (m.d 2 3) (by simp) with h6205 | h6205
                        · linarith only [h4, h6205, hlam]
                        · linarith only [h4716, h6205, hlam]
                    · linarith only [h6202, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    rcases p6198_3 (m.d 0 2) (by simp) with h6209 | h6209
                    · rcases p6198_3 (m.d 1 2) (by simp) with h6210 | h6210
                      · linarith only [h0, h6210, hlam]
                      · rcases p6198_3 (m.d 2 3) (by simp) with h6212 | h6212
                        · linarith only [h4, h6212, hlam]
                        · linarith only [h4717, h6212, hlam]
                    · linarith only [h6209, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h0, hlam, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h10, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h3576, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h4058, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h4, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    rcases p6198_3 (m.d 0 2) (by simp) with h6222 | h6222
                    · rcases p6198_3 (m.d 1 2) (by simp) with h6223 | h6223
                      · linarith only [h6223, hlam, p6198_0]
                      · rcases p6198_3 (m.d 2 3) (by simp) with h6225 | h6225
                        · rcases p6198_3 (m.d 2 4) (by simp) with h6226 | h6226
                          · linarith only [h4716, h6226, hlam]
                          · linarith only [h3576, h6226, hlam]
                        · linarith only [h6225, hlam, p6198_0]
                    · linarith only [h0, h6222, hlam]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h5, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h4716, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h4718, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h6, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    rcases p6198_3 (m.d 0 2) (by simp) with h6240 | h6240
                    · rcases p6198_3 (m.d 1 2) (by simp) with h6241 | h6241
                      · linarith only [h6241, hlam, p6198_0]
                      · rcases p6198_3 (m.d 2 3) (by simp) with h6243 | h6243
                        · rcases p6198_3 (m.d 2 4) (by simp) with h6244 | h6244
                          · linarith only [h4718, h6244, hlam]
                          · linarith only [h3576, h6244, hlam]
                        · linarith only [h10, h6243, hlam]
                    · linarith only [h0, h6240, hlam]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h4717, hlam, p6198_0]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [h0, h3576, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6198_1]
                  · have p6198_0 := h6198c.1
                    have p6198_1 := h6198c.2.1
                    have p6198_2 := h6198c.2.2.1
                    have p6198_3 := h6198c.2.2.2
                    linarith only [hlam, p6198_0]
                · rcases h2bigk with h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c | h6252c
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h10, h3576, h4, h4131, hlam, p5601_1, p6252_2]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h10, h3576, h4131, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    rcases p6252_3 (m.d 0 2) (by simp) with h6256 | h6256
                    · rcases p6252_3 (m.d 1 2) (by simp) with h6257 | h6257
                      · linarith only [h0, h6257, hlam]
                      · rcases p6252_3 (m.d 2 3) (by simp) with h6259 | h6259
                        · linarith only [h4, h6259, hlam]
                        · linarith only [h4716, h6259, hlam]
                    · linarith only [h6256, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    rcases p6252_3 (m.d 0 2) (by simp) with h6263 | h6263
                    · rcases p6252_3 (m.d 1 2) (by simp) with h6264 | h6264
                      · linarith only [h0, h6264, hlam]
                      · rcases p6252_3 (m.d 2 3) (by simp) with h6266 | h6266
                        · linarith only [h4, h6266, hlam]
                        · linarith only [h4717, h6266, hlam]
                    · linarith only [h6263, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h0, hlam, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h10, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h3576, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h4058, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h4, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    rcases p6252_3 (m.d 0 2) (by simp) with h6276 | h6276
                    · rcases p6252_3 (m.d 1 2) (by simp) with h6277 | h6277
                      · linarith only [h6277, hlam, p6252_0]
                      · rcases p6252_3 (m.d 2 3) (by simp) with h6279 | h6279
                        · rcases p6252_3 (m.d 2 4) (by simp) with h6280 | h6280
                          · linarith only [h4716, h6280, hlam]
                          · linarith only [h3576, h6280, hlam]
                        · linarith only [h6279, hlam, p6252_0]
                    · linarith only [h0, h6276, hlam]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h0, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h5, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h4716, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h4718, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h6, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    rcases p6252_3 (m.d 0 2) (by simp) with h6294 | h6294
                    · rcases p6252_3 (m.d 1 2) (by simp) with h6295 | h6295
                      · linarith only [h6295, hlam, p6252_0]
                      · rcases p6252_3 (m.d 2 3) (by simp) with h6297 | h6297
                        · rcases p6252_3 (m.d 2 4) (by simp) with h6298 | h6298
                          · linarith only [h4718, h6298, hlam]
                          · linarith only [h3576, h6298, hlam]
                        · linarith only [h10, h6297, hlam]
                    · linarith only [h0, h6294, hlam]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h4717, hlam, p6252_0]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [h3576, hc12, hc25, hlam, hphi, p6252_1]
                  · have p6252_0 := h6252c.1
                    have p6252_1 := h6252c.2.1
                    have p6252_2 := h6252c.2.2.1
                    have p6252_3 := h6252c.2.2.2
                    linarith only [hlam, p6252_0]
          · linarith only [h4130, h6136, hlam]
      · linarith only [h3, h6133, hlam]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h2, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h0, h4, h4131, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h4129, hlam, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h4131, hlam, p5601_1]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h3, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6314 | h6314
      · rcases p5601_3 (m.d 1 2) (by simp) with h6315 | h6315
        · linarith only [h4058, h6315, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6317 | h6317
          · rcases p5601_3 (m.d 1 4) (by simp) with h6318 | h6318
            · linarith only [h4131, h6318, hlam]
            · linarith only [h3576, h6318, hlam]
          · linarith only [h10, h6317, hlam]
      · linarith only [h0, h6314, hlam]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [h4130, hlam, p5601_0]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      rcases p5601_3 (m.d 0 1) (by simp) with h6324 | h6324
      · rcases p5601_3 (m.d 1 2) (by simp) with h6325 | h6325
        · linarith only [h4058, h6325, hlam]
        · rcases p5601_3 (m.d 1 3) (by simp) with h6327 | h6327
          · rcases p5601_3 (m.d 1 4) (by simp) with h6328 | h6328
            · linarith only [h4131, h6328, hlam]
            · rcases p5601_3 (m.d 1 5) (by simp) with h6330 | h6330
              · rcases h1emax with h6331 | h6331 | h6331 | h6331 | h6331
                · linarith only [h0, h4, h4058, h4718, h6331, h7, h9, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p5601_1]
                · rcases h2bigk with h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c | h6333c
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h3576, h4, h4058, h4718, h7, h9, hlam, p5601_1, p6333_2]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h0, h10, h3576, h4130, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    rcases p6333_3 (m.d 0 2) (by simp) with h6337 | h6337
                    · rcases p6333_3 (m.d 1 2) (by simp) with h6338 | h6338
                      · linarith only [h0, h6338, hlam]
                      · rcases p6333_3 (m.d 2 3) (by simp) with h6340 | h6340
                        · linarith only [h4, h6340, hlam]
                        · linarith only [h4716, h6340, hlam]
                    · linarith only [h6337, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h0, h3576, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h0, hlam, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h10, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h3576, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4058, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    rcases p6333_3 (m.d 0 2) (by simp) with h6351 | h6351
                    · rcases p6333_3 (m.d 1 2) (by simp) with h6352 | h6352
                      · linarith only [h6352, hlam, p6333_0]
                      · rcases p6333_3 (m.d 2 3) (by simp) with h6354 | h6354
                        · rcases p6333_3 (m.d 2 4) (by simp) with h6355 | h6355
                          · linarith only [h4716, h6355, hlam]
                          · linarith only [h3576, h6355, hlam]
                        · linarith only [h6354, hlam, p6333_0]
                    · linarith only [h0, h6351, hlam]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h0, h3576, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h5, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4718, h7, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4716, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4718, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h6, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    rcases p6333_3 (m.d 0 2) (by simp) with h6369 | h6369
                    · rcases p6333_3 (m.d 1 2) (by simp) with h6370 | h6370
                      · linarith only [h6370, hlam, p6333_0]
                      · rcases p6333_3 (m.d 2 3) (by simp) with h6372 | h6372
                        · rcases p6333_3 (m.d 2 4) (by simp) with h6373 | h6373
                          · linarith only [h4718, h6373, hlam]
                          · linarith only [h3576, h6373, hlam]
                        · linarith only [h10, h6372, hlam]
                    · linarith only [h0, h6369, hlam]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h4717, hlam, p6333_0]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [h3576, hc12, hc25, hlam, hphi, p6333_1]
                  · have p6333_0 := h6333c.1
                    have p6333_1 := h6333c.2.1
                    have p6333_2 := h6333c.2.2.1
                    have p6333_3 := h6333c.2.2.2
                    linarith only [hlam, p6333_0]
                · linarith only [h3576, h4130, h6331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5601_1]
                · rcases h2bigk with h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c | h6382c
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h10, h3576, h4, h4130, hlam, p5601_1, p6382_2]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h10, h3576, h4130, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    rcases p6382_3 (m.d 0 2) (by simp) with h6386 | h6386
                    · rcases p6382_3 (m.d 1 2) (by simp) with h6387 | h6387
                      · linarith only [h0, h6387, hlam]
                      · rcases p6382_3 (m.d 2 3) (by simp) with h6389 | h6389
                        · linarith only [h4, h6389, hlam]
                        · linarith only [h4716, h6389, hlam]
                    · linarith only [h6386, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h0, h3576, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h0, hlam, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h10, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h3576, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h4058, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h4, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    rcases p6382_3 (m.d 0 2) (by simp) with h6400 | h6400
                    · rcases p6382_3 (m.d 1 2) (by simp) with h6401 | h6401
                      · linarith only [h6401, hlam, p6382_0]
                      · rcases p6382_3 (m.d 2 3) (by simp) with h6403 | h6403
                        · rcases p6382_3 (m.d 2 4) (by simp) with h6404 | h6404
                          · linarith only [h4716, h6404, hlam]
                          · linarith only [h3576, h6404, hlam]
                        · linarith only [h6403, hlam, p6382_0]
                    · linarith only [h0, h6400, hlam]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h3576, hc12, hc23, hlam, hphi, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h0, h3576, h4, h4058, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5601_1, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h5, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h0, h4, h4718, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h4716, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h4718, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h6, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    rcases p6382_3 (m.d 0 2) (by simp) with h6418 | h6418
                    · rcases p6382_3 (m.d 1 2) (by simp) with h6419 | h6419
                      · linarith only [h6419, hlam, p6382_0]
                      · rcases p6382_3 (m.d 2 3) (by simp) with h6421 | h6421
                        · rcases p6382_3 (m.d 2 4) (by simp) with h6422 | h6422
                          · linarith only [h4718, h6422, hlam]
                          · linarith only [h3576, h6422, hlam]
                        · linarith only [h10, h6421, hlam]
                    · linarith only [h0, h6418, hlam]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h4717, hlam, p6382_0]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [h3576, hc12, hc25, hlam, hphi, p6382_1]
                  · have p6382_0 := h6382c.1
                    have p6382_1 := h6382c.2.1
                    have p6382_2 := h6382c.2.2.1
                    have p6382_3 := h6382c.2.2.2
                    linarith only [hlam, p6382_0]
                · linarith only [h3576, h6331, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5601_1]
              · linarith only [h4131, h6330, hlam]
          · linarith only [h4129, h6327, hlam]
      · linarith only [h2, h6324, hlam]
    · have p5601_0 := h5601c.1
      have p5601_1 := h5601c.2.1
      have p5601_2 := h5601c.2.2.1
      have p5601_3 := h5601c.2.2.2
      linarith only [hlam, p5601_0]

set_option maxHeartbeats 5636000 in
set_option maxHeartbeats 5636000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg3576 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg4058 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (hg4129 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h4130 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h4131 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
    (h4716 : (m.d 2 3 + m.lam ≤ m.d 3 4 ∧ m.d 2 3 < m.d 2 4 ∧ m.d 2 4 < m.d 3 4))
    (h4717 : (m.d 2 3 + m.lam ≤ m.d 3 5 ∧ m.d 2 3 < m.d 2 5 ∧ m.d 2 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
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
  have h9 := hg9
  have h10 := hg10
  have h3576 := hg3576
  have h4058 := hg4058
  have h4129 := hg4129
  rcases m.htr 2 4 5 (by decide) (by decide) with h4718 | h4718
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s16_x0_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10 hg3576 hg4058 hg4129 h4130 h4131 h4716 h4717 h4718

end R2N4
