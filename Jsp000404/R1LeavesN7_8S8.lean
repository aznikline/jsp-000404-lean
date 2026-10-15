import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h4107 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 0 4 5 (by decide) (by decide) with h5581 | h5581
  · linarith only [h4106, h4107, h5581, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5583 | h5583
    · linarith only [h0, h4, h5583, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5585 | h5585
      · linarith only [h0, h3476, h5585, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5587 | h5587
        · linarith only [h0, h4023, h5587, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5589 | h5589
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5590 | h5590
            · linarith only [h1, h4107, h5590, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5592 | h5592
              · linarith only [h2, h5581, h5592, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5594 | h5594
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5595 | h5595
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5596 | h5596
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5597 | h5597
                      · linarith only [h4106, h4107, h5581, h5595, h5597, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases h0bigk with h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c | h5599c
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          rcases p5599_3 (m.d 0 1) (by simp) with h5601 | h5601
                          · rcases p5599_3 (m.d 0 2) (by simp) with h5602 | h5602
                            · linarith only [h0, h5602, hlam]
                            · rcases p5599_3 (m.d 0 3) (by simp) with h5604 | h5604
                              · linarith only [h1, h5604, hlam]
                              · linarith only [h4, h5604, hlam]
                          · linarith only [h0, h5601, hlam]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          rcases p5599_3 (m.d 0 1) (by simp) with h5608 | h5608
                          · rcases p5599_3 (m.d 0 2) (by simp) with h5609 | h5609
                            · linarith only [h0, h5609, hlam]
                            · rcases p5599_3 (m.d 0 3) (by simp) with h5611 | h5611
                              · linarith only [h1, h5611, hlam]
                              · rcases p5599_3 (m.d 0 4) (by simp) with h5613 | h5613
                                · linarith only [h2, h5613, hlam]
                                · rcases p5599_3 (m.d 0 5) (by simp) with h5615 | h5615
                                  · linarith only [h3, h5615, hlam]
                                  · linarith only [h4107, h5615, hlam]
                          · linarith only [h1, h5608, hlam]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          rcases p5599_3 (m.d 0 1) (by simp) with h5619 | h5619
                          · rcases p5599_3 (m.d 0 2) (by simp) with h5620 | h5620
                            · linarith only [h0, h5620, hlam]
                            · rcases p5599_3 (m.d 0 3) (by simp) with h5622 | h5622
                              · linarith only [h1, h5622, hlam]
                              · linarith only [h4106, h5622, hlam]
                          · linarith only [h2, h5619, hlam]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          rcases p5599_3 (m.d 0 1) (by simp) with h5626 | h5626
                          · rcases p5599_3 (m.d 0 2) (by simp) with h5627 | h5627
                            · linarith only [h0, h5627, hlam]
                            · rcases p5599_3 (m.d 0 3) (by simp) with h5629 | h5629
                              · linarith only [h1, h5629, hlam]
                              · rcases p5599_3 (m.d 0 4) (by simp) with h5631 | h5631
                                · linarith only [h2, h5631, hlam]
                                · rcases p5599_3 (m.d 0 5) (by simp) with h5633 | h5633
                                  · linarith only [h3, h5633, hlam]
                                  · rcases h2bigk with h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c | h5635c
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h4, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h3476, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h4023, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h0, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5583, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5585, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5587, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5646 | h5646
                                      · linarith only [h5646, hlam, p5635_0]
                                      · rcases p5635_3 (m.d 1 2) (by simp) with h5648 | h5648
                                        · linarith only [h5583, h5648, hlam]
                                        · rcases p5635_3 (m.d 2 3) (by simp) with h5650 | h5650
                                          · rcases p5635_3 (m.d 2 4) (by simp) with h5651 | h5651
                                            · linarith only [h5594, h5651, hlam]
                                            · linarith only [h3476, h5651, hlam]
                                          · linarith only [h5650, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5655 | h5655
                                      · linarith only [h4, h5655, hlam]
                                      · linarith only [h0, h5655, hlam]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h1, h4107, h5589, h5596, h5597, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h1, h4107, h5589, h5596, h5597, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5661 | h5661
                                      · linarith only [h5661, hlam, p5635_0]
                                      · rcases p5635_3 (m.d 1 2) (by simp) with h5663 | h5663
                                        · linarith only [h5585, h5663, hlam]
                                        · rcases p5635_3 (m.d 2 3) (by simp) with h5665 | h5665
                                          · rcases p5635_3 (m.d 2 4) (by simp) with h5666 | h5666
                                            · rcases p5635_3 (m.d 2 5) (by simp) with h5667 | h5667
                                              · linarith only [h5596, h5667, hlam]
                                              · linarith only [h4023, h5667, hlam]
                                            · linarith only [h5666, hlam, p5635_0]
                                          · linarith only [h4, h5665, hlam]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5672 | h5672
                                      · linarith only [h3476, h5672, hlam]
                                      · linarith only [h0, h5672, hlam]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5594, hlam, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h1, h4107, h5589, h5596, h5597, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5678 | h5678
                                      · linarith only [h5678, hlam, p5635_0]
                                      · rcases p5635_3 (m.d 1 2) (by simp) with h5680 | h5680
                                        · linarith only [h5587, h5680, hlam]
                                        · rcases p5635_3 (m.d 2 3) (by simp) with h5682 | h5682
                                          · rcases p5635_3 (m.d 2 4) (by simp) with h5683 | h5683
                                            · rcases p5635_3 (m.d 2 5) (by simp) with h5684 | h5684
                                              · rcases h3bigk with h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c | h5685c
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4107, h5589, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4, hlam, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5599_1, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4107, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h1, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5583, hlam, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h1, h4107, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5599_1, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5590, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  rcases p5685_3 (m.d 0 3) (by simp) with h5696 | h5696
                                                  · linarith only [h4, h5696, hlam]
                                                  · rcases p5685_3 (m.d 1 3) (by simp) with h5698 | h5698
                                                    · linarith only [h5583, h5698, hlam]
                                                    · rcases p5685_3 (m.d 2 3) (by simp) with h5700 | h5700
                                                      · rcases p5685_3 (m.d 3 4) (by simp) with h5701 | h5701
                                                        · linarith only [h5594, h5701, hlam]
                                                        · rcases p5685_3 (m.d 3 5) (by simp) with h5703 | h5703
                                                          · linarith only [h5595, h5703, hlam]
                                                          · linarith only [h4107, h5703, hlam]
                                                      · linarith only [h4, h5700, hlam]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  rcases p5685_3 (m.d 0 3) (by simp) with h5707 | h5707
                                                  · linarith only [h4, h5707, hlam]
                                                  · linarith only [h1, h5707, hlam]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4106, h4107, h5594, h5596, h5597, hlam, p5685_2]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h1, h4107, h5589, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h4106, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5589, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5594, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5597, hlam, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h1, h5589, h5595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5589, h5595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5685_1]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [h5595, hlam, p5685_0]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  rcases p5685_3 (m.d 0 3) (by simp) with h5721 | h5721
                                                  · linarith only [h4107, h5721, hlam]
                                                  · linarith only [h4106, h5721, hlam]
                                                · have p5685_0 := h5685c.1
                                                  have p5685_1 := h5685c.2.1
                                                  have p5685_2 := h5685c.2.2.1
                                                  have p5685_3 := h5685c.2.2.2
                                                  linarith only [hlam, p5685_0]
                                              · linarith only [h5684, hlam, p5635_0]
                                            · linarith only [h3476, h5683, hlam]
                                          · linarith only [h4, h5682, hlam]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      rcases p5635_3 (m.d 0 2) (by simp) with h5728 | h5728
                                      · linarith only [h4023, h5728, hlam]
                                      · linarith only [h0, h5728, hlam]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5595, hlam, p5635_1]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [h5596, hlam, p5635_0]
                                    · have p5635_0 := h5635c.1
                                      have p5635_1 := h5635c.2.1
                                      have p5635_2 := h5635c.2.2.1
                                      have p5635_3 := h5635c.2.2.2
                                      linarith only [hlam, p5635_0]
                          · linarith only [h3, h5626, hlam]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h0, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h4, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h3476, hlam, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h4023, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h1, hlam, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h0, h4107, h5594, h5596, h5597, hc12, hc23, hlam, hphi, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h2, h4107, h5585, h5594, h5596, h5597, hc12, hc23, hlam, hphi, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h4107, hlam, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h2, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h0, h4106, h4107, h5594, h5596, h5597, hc12, hc23, hlam, hphi, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h4106, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h5581, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h3, hlam, p5599_0]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h0, h4107, h5594, h5596, h5597, hc12, hc23, hlam, hphi, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h1, h4107, h5589, h5594, h5596, h5597, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [h2, h4107, h5585, h5594, h5596, h5597, hc12, hc23, hlam, hphi, p5599_1]
                        · have p5599_0 := h5599c.1
                          have p5599_1 := h5599c.2.1
                          have p5599_2 := h5599c.2.2.1
                          have p5599_3 := h5599c.2.2.2
                          linarith only [hlam, p5599_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5755 | h5755
                      · linarith only [h1, h5589, h5596, h5755, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h0bigk with h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c | h5757c
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          rcases p5757_3 (m.d 0 1) (by simp) with h5759 | h5759
                          · rcases p5757_3 (m.d 0 2) (by simp) with h5760 | h5760
                            · linarith only [h0, h5760, hlam]
                            · rcases p5757_3 (m.d 0 3) (by simp) with h5762 | h5762
                              · linarith only [h1, h5762, hlam]
                              · linarith only [h4, h5762, hlam]
                          · linarith only [h0, h5759, hlam]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          rcases p5757_3 (m.d 0 1) (by simp) with h5766 | h5766
                          · rcases p5757_3 (m.d 0 2) (by simp) with h5767 | h5767
                            · linarith only [h0, h5767, hlam]
                            · rcases p5757_3 (m.d 0 3) (by simp) with h5769 | h5769
                              · linarith only [h1, h5769, hlam]
                              · rcases p5757_3 (m.d 0 4) (by simp) with h5771 | h5771
                                · linarith only [h2, h5771, hlam]
                                · rcases p5757_3 (m.d 0 5) (by simp) with h5773 | h5773
                                  · linarith only [h3, h5773, hlam]
                                  · linarith only [h4107, h5773, hlam]
                          · linarith only [h1, h5766, hlam]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          rcases p5757_3 (m.d 0 1) (by simp) with h5777 | h5777
                          · rcases p5757_3 (m.d 0 2) (by simp) with h5778 | h5778
                            · linarith only [h0, h5778, hlam]
                            · rcases p5757_3 (m.d 0 3) (by simp) with h5780 | h5780
                              · linarith only [h1, h5780, hlam]
                              · linarith only [h4106, h5780, hlam]
                          · linarith only [h2, h5777, hlam]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          rcases p5757_3 (m.d 0 1) (by simp) with h5784 | h5784
                          · rcases p5757_3 (m.d 0 2) (by simp) with h5785 | h5785
                            · linarith only [h0, h5785, hlam]
                            · rcases p5757_3 (m.d 0 3) (by simp) with h5787 | h5787
                              · linarith only [h1, h5787, hlam]
                              · rcases p5757_3 (m.d 0 4) (by simp) with h5789 | h5789
                                · linarith only [h2, h5789, hlam]
                                · rcases p5757_3 (m.d 0 5) (by simp) with h5791 | h5791
                                  · linarith only [h3, h5791, hlam]
                                  · rcases h2bigk with h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c | h5793c
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h3476, hc12, hc24, hlam, hphi, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h4, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h3476, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h4023, hlam, p5793_0]
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
                                      linarith only [h5583, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5585, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5587, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      rcases p5793_3 (m.d 0 2) (by simp) with h5804 | h5804
                                      · linarith only [h5804, hlam, p5793_0]
                                      · rcases p5793_3 (m.d 1 2) (by simp) with h5806 | h5806
                                        · linarith only [h5583, h5806, hlam]
                                        · rcases p5793_3 (m.d 2 3) (by simp) with h5808 | h5808
                                          · rcases p5793_3 (m.d 2 4) (by simp) with h5809 | h5809
                                            · linarith only [h5594, h5809, hlam]
                                            · linarith only [h3476, h5809, hlam]
                                          · linarith only [h5808, hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      rcases p5793_3 (m.d 0 2) (by simp) with h5813 | h5813
                                      · linarith only [h4, h5813, hlam]
                                      · linarith only [h0, h5813, hlam]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h3476, hc02, hc23, hlam, hphi, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h1, h4107, h5589, h5595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h0, h5596, hc12, hc45, hlam, hphi, ht23, ht34, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5596, hc12, hc45, hlam, hphi, ht23, ht34, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5594, hlam, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [hlam, p5793_0]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5596, hlam, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      rcases p5793_3 (m.d 0 2) (by simp) with h5824 | h5824
                                      · linarith only [h5824, hlam, p5793_0]
                                      · rcases p5793_3 (m.d 1 2) (by simp) with h5826 | h5826
                                        · linarith only [h5587, h5826, hlam]
                                        · rcases p5793_3 (m.d 2 3) (by simp) with h5828 | h5828
                                          · rcases p5793_3 (m.d 2 4) (by simp) with h5829 | h5829
                                            · linarith only [h5596, h5829, hlam]
                                            · linarith only [h3476, h5829, hlam]
                                          · linarith only [h4, h5828, hlam]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      rcases p5793_3 (m.d 0 2) (by simp) with h5833 | h5833
                                      · linarith only [h4023, h5833, hlam]
                                      · linarith only [h0, h5833, hlam]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h5595, hlam, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [h0, h3476, hc12, hc25, hlam, hphi, p5793_1]
                                    · have p5793_0 := h5793c.1
                                      have p5793_1 := h5793c.2.1
                                      have p5793_2 := h5793c.2.2.1
                                      have p5793_3 := h5793c.2.2.2
                                      linarith only [hlam, p5793_0]
                          · linarith only [h3, h5784, hlam]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h0, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h4, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h3476, hlam, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h4023, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h1, hlam, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h0, h4107, hc12, hc35, hlam, hphi, ht23, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h2, h4107, h5585, hc12, hc35, hlam, hphi, ht23, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h4107, hlam, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h2, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h0, h4106, h4107, hc12, hc35, hlam, hphi, ht23, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h4106, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h5581, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h3, hlam, p5757_0]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h0, h4107, h5595, hc12, hc23, hlam, hphi, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h1, h4107, h5589, h5595, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [h2, h4107, h5585, h5595, hc12, hc23, hlam, hphi, p5757_1]
                        · have p5757_0 := h5757c.1
                          have p5757_1 := h5757c.2.1
                          have p5757_2 := h5757c.2.2.1
                          have p5757_3 := h5757c.2.2.2
                          linarith only [hlam, p5757_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5860 | h5860
                    · linarith only [h2, h5581, h5585, h5594, h5595, h5860, hc12, hc35, hlam, hphi, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5862 | h5862
                      · linarith only [h0, h1, h3476, h5589, h5860, h5862, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h0bigk with h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c | h5864c
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5866 | h5866
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5867 | h5867
                            · linarith only [h0, h5867, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5869 | h5869
                              · linarith only [h1, h5869, hlam]
                              · linarith only [h4, h5869, hlam]
                          · linarith only [h0, h5866, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5873 | h5873
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5874 | h5874
                            · linarith only [h0, h5874, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5876 | h5876
                              · linarith only [h1, h5876, hlam]
                              · rcases p5864_3 (m.d 0 4) (by simp) with h5878 | h5878
                                · linarith only [h2, h5878, hlam]
                                · rcases p5864_3 (m.d 0 5) (by simp) with h5880 | h5880
                                  · linarith only [h3, h5880, hlam]
                                  · linarith only [h4107, h5880, hlam]
                          · linarith only [h1, h5873, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5884 | h5884
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5885 | h5885
                            · linarith only [h0, h5885, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5887 | h5887
                              · linarith only [h1, h5887, hlam]
                              · linarith only [h4106, h5887, hlam]
                          · linarith only [h2, h5884, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5891 | h5891
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5892 | h5892
                            · linarith only [h0, h5892, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5894 | h5894
                              · linarith only [h1, h5894, hlam]
                              · rcases p5864_3 (m.d 0 4) (by simp) with h5896 | h5896
                                · linarith only [h2, h5896, hlam]
                                · rcases p5864_3 (m.d 0 5) (by simp) with h5898 | h5898
                                  · linarith only [h3, h5898, hlam]
                                  · rcases h2bigk with h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c | h5900c
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h3476, hc12, hc24, hlam, hphi, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h4, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h3476, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h4023, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h0, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5583, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5585, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5587, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5595, h5862, hc02, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5595, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5595, h5862, hc24, hc45, hlam, hphi, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5595, hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h0, h5594, h5595, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5594, h5595, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5594, hlam, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [hlam, p5900_0]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h5860, hlam, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      rcases p5900_3 (m.d 0 2) (by simp) with h5921 | h5921
                                      · linarith only [h5921, hlam, p5900_0]
                                      · rcases p5900_3 (m.d 1 2) (by simp) with h5923 | h5923
                                        · linarith only [h5587, h5923, hlam]
                                        · rcases p5900_3 (m.d 2 3) (by simp) with h5925 | h5925
                                          · linarith only [h5595, h5925, hlam]
                                          · linarith only [h4, h5925, hlam]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      rcases p5900_3 (m.d 0 2) (by simp) with h5928 | h5928
                                      · linarith only [h4023, h5928, hlam]
                                      · linarith only [h0, h5928, hlam]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h0, h4, h5595, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [h0, h3476, h5595, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5900_1]
                                    · have p5900_0 := h5900c.1
                                      have p5900_1 := h5900c.2.1
                                      have p5900_2 := h5900c.2.2.1
                                      have p5900_3 := h5900c.2.2.2
                                      linarith only [hlam, p5900_0]
                          · linarith only [h3, h5891, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h0, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h4, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h3476, hlam, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h4023, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h1, hlam, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h0, h4107, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h0, h3476, h4107, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h4107, hlam, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h2, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h0, h4106, h4107, h5862, hc12, hc45, hlam, hphi, ht23, ht34, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h4106, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h5581, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h3, hlam, p5864_0]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5951 | h5951
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5952 | h5952
                            · linarith only [h4023, h5952, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5954 | h5954
                              · linarith only [h4107, h5954, hlam]
                              · linarith only [h4, h5954, hlam]
                          · linarith only [h0, h5951, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [h1, h4023, h5589, h5595, h5862, hc34, hc45, hlam, hphi, p5864_1]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          rcases p5864_3 (m.d 0 1) (by simp) with h5959 | h5959
                          · rcases p5864_3 (m.d 0 2) (by simp) with h5960 | h5960
                            · linarith only [h4023, h5960, hlam]
                            · rcases p5864_3 (m.d 0 3) (by simp) with h5962 | h5962
                              · linarith only [h4107, h5962, hlam]
                              · linarith only [h4106, h5962, hlam]
                          · linarith only [h2, h5959, hlam]
                        · have p5864_0 := h5864c.1
                          have p5864_1 := h5864c.2.1
                          have p5864_2 := h5864c.2.2.1
                          have p5864_3 := h5864c.2.2.2
                          linarith only [hlam, p5864_0]
                · linarith only [h0, h1, h4, h5589, h5594, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · linarith only [h4106, h4107, h5589, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 0 3 5 (by decide) (by decide) with h4107 | h4107
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106 h4107
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106 h4107

end R2N4
