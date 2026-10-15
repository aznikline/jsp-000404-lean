import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11630000 in
set_option maxHeartbeats 11630000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_13_25_L_I_L_I_H_I_s8 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7 h8
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5605 | h5605
    · linarith only [h5605, h7, h8, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5607 | h5607
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5608 | h5608
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5609 | h5609
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5610 | h5610
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5611 | h5611
              · linarith only [h1, h5611, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5613 | h5613
                · linarith only [h2, h5605, h5613, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5615 | h5615
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5616 | h5616
                    · linarith only [h1, h5607, h5616, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5618 | h5618
                      · linarith only [h2, h5605, h5608, h5618, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5620 | h5620
                        · linarith only [h0, h5605, h5609, h5615, h5616, h5620, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h1bigk with h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c | h5622c
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5609, h5615, h5616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            rcases p5622_3 (m.d 0 1) (by simp) with h5625 | h5625
                            · rcases p5622_3 (m.d 1 2) (by simp) with h5626 | h5626
                              · linarith only [h0, h5626, hlam]
                              · linarith only [h5607, h5626, hlam]
                            · linarith only [h5625, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            rcases p5622_3 (m.d 0 1) (by simp) with h5630 | h5630
                            · rcases p5622_3 (m.d 1 2) (by simp) with h5631 | h5631
                              · linarith only [h0, h5631, hlam]
                              · linarith only [h5608, h5631, hlam]
                            · linarith only [h5630, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            rcases p5622_3 (m.d 0 1) (by simp) with h5635 | h5635
                            · rcases p5622_3 (m.d 1 2) (by simp) with h5636 | h5636
                              · linarith only [h0, h5636, hlam]
                              · linarith only [h5609, h5636, hlam]
                            · linarith only [h5635, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h0, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h0, h5607, h5615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            rcases p5622_3 (m.d 0 1) (by simp) with h5643 | h5643
                            · rcases p5622_3 (m.d 1 2) (by simp) with h5644 | h5644
                              · rcases p5622_3 (m.d 1 3) (by simp) with h5645 | h5645
                                · linarith only [h5607, h5645, hlam]
                                · linarith only [h5610, h5645, hlam]
                              · linarith only [h5608, h5644, hlam]
                            · linarith only [h2, h5643, hlam]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h0, h5609, h5615, h5616, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h1, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5607, hlam, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h1, h5608, h5615, h5620, h8, hc34, hc45, hlam, hphi, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5611, hlam, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h2, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5608, hlam, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5610, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5613, hlam, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h3, hlam, p5622_0]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h5609, hlam, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [h3, h5607, h5615, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5622_1]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            rcases p5622_3 (m.d 0 1) (by simp) with h5664 | h5664
                            · rcases p5622_3 (m.d 1 2) (by simp) with h5665 | h5665
                              · rcases p5622_3 (m.d 1 3) (by simp) with h5666 | h5666
                                · linarith only [h5611, h5666, hlam]
                                · linarith only [h5610, h5666, hlam]
                              · linarith only [h5608, h5665, hlam]
                            · linarith only [h2, h5664, hlam]
                          · have p5622_0 := h5622c.1
                            have p5622_1 := h5622c.2.1
                            have p5622_2 := h5622c.2.2.1
                            have p5622_3 := h5622c.2.2.2
                            linarith only [hlam, p5622_0]
                  · linarith only [h5615, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h5607, h5610, h7, h8, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5674 | h5674
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5675 | h5675
              · linarith only [h5607, h5609, h5675, h6, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5677 | h5677
                · linarith only [h2, h5605, h5677, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5679 | h5679
                  · linarith only [h0, h5607, h5609, h5679, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h5679, h7, h8, hc23, hc35, hlam, hphi]
            · linarith only [h5674, h7, h8, hc13, hc35, hlam, hphi]
        · linarith only [h5, h5607, h5608, h7, h8, hc23, hc35, hlam, hphi]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5684 | h5684
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5685 | h5685
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5686 | h5686
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5687 | h5687
              · linarith only [h4, h5607, h5684, h5687, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h5607, h5685, h5687, hlam]
            · linarith only [h5607, h5684, h5686, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5691 | h5691
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5692 | h5692
              · linarith only [h1, h5692, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5694 | h5694
                · linarith only [h2, h5605, h5694, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5696 | h5696
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5697 | h5697
                    · linarith only [h4, h5697, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5699 | h5699
                      · linarith only [h4, h5605, h5607, h5684, h5699, h8, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5701 | h5701
                        · linarith only [h4, h5605, h5607, h5684, h5696, h5701, h8, hlam]
                        · linarith only [h4, h5607, h5684, h5696, h5701, h8, hc34, hc45, hlam, hphi]
                  · linarith only [h5607, h5696, h7, h8, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h5691, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5706 | h5706
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5707 | h5707
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5708 | h5708
              · linarith only [h1, h5708, h8, hlam]
              · linarith only [h5607, h5706, h5708, hlam]
            · linarith only [h5607, h5706, h5707, h7, h8, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5712 | h5712
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5713 | h5713
              · linarith only [h1, h5713, h8, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5715 | h5715
                · linarith only [h2, h5, h5605, h5684, h5715, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5717 | h5717
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5718 | h5718
                    · linarith only [h4, h5718, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5720 | h5720
                      · linarith only [h5, h5605, h5720, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5722 | h5722
                        · linarith only [h5, h5605, h5684, h5722, hc12, hc34, hlam, hphi, ht23]
                        · rcases h1bigk with h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c | h5724c
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5726 | h5726
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5727 | h5727
                              · linarith only [h5727, hlam, p5724_0]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5729 | h5729
                                · linarith only [h1, h5729, hlam]
                                · linarith only [h5607, h5729, hlam]
                            · linarith only [h5726, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5733 | h5733
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5734 | h5734
                              · linarith only [h0, h5734, hlam]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5736 | h5736
                                · linarith only [h5736, hlam, p5724_0]
                                · rcases p5724_3 (m.d 1 4) (by simp) with h5738 | h5738
                                  · linarith only [h2, h5738, hlam]
                                  · rcases p5724_3 (m.d 1 5) (by simp) with h5740 | h5740
                                    · linarith only [h3, h5740, hlam]
                                    · linarith only [h5713, h5740, hlam]
                            · linarith only [h5733, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5744 | h5744
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5745 | h5745
                              · linarith only [h0, h5745, hlam]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5747 | h5747
                                · linarith only [h1, h5747, hlam]
                                · linarith only [h5712, h5747, hlam]
                            · linarith only [h5744, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5751 | h5751
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5752 | h5752
                              · linarith only [h0, h5752, hlam]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5754 | h5754
                                · linarith only [h1, h5754, hlam]
                                · rcases p5724_3 (m.d 1 4) (by simp) with h5756 | h5756
                                  · linarith only [h2, h5756, hlam]
                                  · rcases p5724_3 (m.d 1 5) (by simp) with h5758 | h5758
                                    · linarith only [h5758, hlam, p5724_0]
                                    · rcases h3bigk with h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c | h5760c
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5712, h8, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h8, hc23, hc35, hlam, hphi, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5722, h8, hc34, hc45, hlam, hphi, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h8, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h1, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5607, hlam, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5713, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5724_1, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5713, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h4, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h4, h5722, h8, hc13, hc45, hlam, hphi, ht34, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h4, h5722, h8, hc34, hc45, hlam, hphi, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5718, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h7, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5712, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5717, hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [hlam, p5760_0]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5722, hlam, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h1, h5712, h5722, hc34, hc45, hlam, hphi, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5712, h5722, hc34, hc45, hlam, hphi, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [h5684, h5717, h5722, hc12, hc45, hlam, hphi, ht23, ht34, p5760_1]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        rcases p5760_3 (m.d 0 3) (by simp) with h5784 | h5784
                                        · linarith only [h5784, h8, hlam]
                                        · linarith only [h5784, h7, hlam]
                                      · have p5760_0 := h5760c.1
                                        have p5760_1 := h5760c.2.1
                                        have p5760_2 := h5760c.2.2.1
                                        have p5760_3 := h5760c.2.2.2
                                        linarith only [hlam, p5760_0]
                            · linarith only [h5751, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h0, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5607, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5684, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5706, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h1, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h1, h5722, h8, hc12, hc45, hlam, hphi, ht23, ht34, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h4, h5607, h5722, h8, hc14, hc45, hlam, hphi, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5713, hlam, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h2, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h2, h5722, h7, h8, hc12, hc45, hlam, hphi, ht23, ht34, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5712, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h5715, hlam, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h3, hlam, p5724_0]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5805 | h5805
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5806 | h5806
                              · linarith only [h5706, h5806, hlam]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5808 | h5808
                                · linarith only [h5713, h5808, hlam]
                                · linarith only [h5607, h5808, hlam]
                            · linarith only [h0, h5805, hlam]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [h3, h5712, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p5724_1]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            rcases p5724_3 (m.d 0 1) (by simp) with h5813 | h5813
                            · rcases p5724_3 (m.d 1 2) (by simp) with h5814 | h5814
                              · linarith only [h5706, h5814, hlam]
                              · rcases p5724_3 (m.d 1 3) (by simp) with h5816 | h5816
                                · linarith only [h5713, h5816, hlam]
                                · linarith only [h5712, h5816, hlam]
                            · linarith only [h2, h5813, hlam]
                          · have p5724_0 := h5724c.1
                            have p5724_1 := h5724c.2.1
                            have p5724_2 := h5724c.2.2.1
                            have p5724_3 := h5724c.2.2.2
                            linarith only [hlam, p5724_0]
                  · linarith only [h1, h5712, h5717, h8, hc23, hc35, hlam, hphi]
            · linarith only [h5712, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  exact r1l7_11_13_25_L_I_L_I_H_I_s7 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5 h6 h7

set_option maxHeartbeats 16094000 in
set_option maxHeartbeats 16094000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s6_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5823 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h5824 | h5824
  · rcases m.htr 1 2 3 (by decide) (by decide) with h5825 | h5825
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5826 | h5826
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5827 | h5827
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5828 | h5828
          · linarith only [h1, h5828, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5830 | h5830
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5831 | h5831
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5832 | h5832
                · linarith only [h1, h5825, h5832, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5834 | h5834
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5835 | h5835
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5836 | h5836
                      · rcases h1bigk with h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c | h5837c
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5826, h5832, h5834, hc01, hc35, hlam, hphi, ht0b, ht5b, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5840 | h5840
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5841 | h5841
                            · linarith only [h0, h5841, hlam]
                            · linarith only [h5825, h5841, hlam]
                          · linarith only [h5840, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5845 | h5845
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5846 | h5846
                            · linarith only [h0, h5846, hlam]
                            · linarith only [h5826, h5846, hlam]
                          · linarith only [h5845, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5850 | h5850
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5851 | h5851
                            · linarith only [h0, h5851, hlam]
                            · linarith only [h5827, h5851, hlam]
                          · linarith only [h5850, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h0, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h0, h5825, h5834, h5836, hc01, hc45, hlam, hphi, ht0b, ht5b, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h0, h5825, h5828, h5834, h5836, hc01, hc45, hlam, hphi, ht0b, ht5b, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5859 | h5859
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5860 | h5860
                            · rcases p5837_3 (m.d 1 3) (by simp) with h5861 | h5861
                              · linarith only [h5825, h5861, hlam]
                              · linarith only [h5830, h5861, hlam]
                            · linarith only [h5827, h5860, hlam]
                          · linarith only [h3, h5859, hlam]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h1, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5825, hlam, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5828, hlam, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5870 | h5870
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5871 | h5871
                            · rcases p5837_3 (m.d 1 3) (by simp) with h5872 | h5872
                              · rcases p5837_3 (m.d 1 4) (by simp) with h5873 | h5873
                                · rcases p5837_3 (m.d 1 5) (by simp) with h5874 | h5874
                                  · linarith only [h5830, h5874, hlam]
                                  · rcases h3bigk with h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c | h5876c
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5827, h5834, h5836, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5837_1, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h7, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      rcases p5876_3 (m.d 0 3) (by simp) with h5881 | h5881
                                      · rcases p5876_3 (m.d 1 3) (by simp) with h5882 | h5882
                                        · linarith only [h1, h5882, hlam]
                                        · linarith only [h5830, h5882, hlam]
                                      · linarith only [h5881, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h1, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h1, h5834, h5836, hc01, hc45, hlam, hphi, ht0b, ht5b, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5828, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      rcases p5876_3 (m.d 0 3) (by simp) with h5890 | h5890
                                      · rcases p5876_3 (m.d 1 3) (by simp) with h5891 | h5891
                                        · rcases p5876_3 (m.d 2 3) (by simp) with h5892 | h5892
                                          · linarith only [h5825, h5892, hlam]
                                          · linarith only [h5834, h5892, hlam]
                                        · linarith only [h5891, hlam, p5876_0]
                                      · linarith only [h5823, h5890, hlam]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h4, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5825, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5832, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h0, h5825, h5836, hc01, hc45, hlam, hphi, ht0b, ht5b, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h1, h5827, h5834, h5836, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5837_1, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5827, h5834, h5836, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5837_1, p5876_1]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      rcases p5876_3 (m.d 0 3) (by simp) with h5904 | h5904
                                      · linarith only [h5904, h7, hlam]
                                      · linarith only [h4, h5904, hlam]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h1, h5827, h5834, h7, hlam, p5837_1, p5876_2]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5823, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5830, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5834, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [h5836, hlam, p5876_0]
                                    · have p5876_0 := h5876c.1
                                      have p5876_1 := h5876c.2.1
                                      have p5876_2 := h5876c.2.2.1
                                      have p5876_3 := h5876c.2.2.2
                                      linarith only [hlam, p5876_0]
                                · linarith only [h5831, h5873, hlam]
                              · linarith only [h5830, h5872, hlam]
                            · linarith only [h5827, h5871, hlam]
                          · linarith only [h3, h5870, hlam]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h2, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5826, hlam, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h0, h5826, h5830, h5836, hc01, hc45, hlam, hphi, ht0b, ht5b, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          rcases p5837_3 (m.d 0 1) (by simp) with h5922 | h5922
                          · rcases p5837_3 (m.d 1 2) (by simp) with h5923 | h5923
                            · rcases p5837_3 (m.d 1 3) (by simp) with h5924 | h5924
                              · linarith only [h5828, h5924, hlam]
                              · linarith only [h5830, h5924, hlam]
                            · linarith only [h5827, h5923, hlam]
                          · linarith only [h3, h5922, hlam]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h3, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5827, hlam, p5837_1]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5830, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [h5831, hlam, p5837_0]
                        · have p5837_0 := h5837c.1
                          have p5837_1 := h5837c.2.1
                          have p5837_2 := h5837c.2.2.1
                          have p5837_3 := h5837c.2.2.2
                          linarith only [hlam, p5837_0]
                      · linarith only [h5824, h5836, h7, hlam]
                    · linarith only [h2, h5831, h5832, h5834, h5835, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h5830, h5834, h7, hc23, hc34, hlam, hphi]
              · linarith only [h5828, h5830, h5831, hlam]
            · linarith only [h5823, h5830, h7, hc13, hc34, hlam, hphi]
        · linarith only [h5823, h5825, h5827, h6, h7, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5940 | h5940
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5941 | h5941
          · linarith only [h1, h5823, h5941, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5943 | h5943
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5944 | h5944
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5945 | h5945
                · linarith only [h5, h5825, h5826, h5945, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5947 | h5947
                  · linarith only [h0, h5, h5825, h5826, h5947, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1, h5943, h5947, h7, hc23, hc34, hlam, hphi]
              · linarith only [h5823, h5824, h5825, h5826, h5944, h7, hc23, hc34, hlam, hphi]
            · linarith only [h5823, h5943, h7, hc13, hc34, hlam, hphi]
        · linarith only [h5823, h5825, h5940, h6, h7, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h5953 | h5953
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5954 | h5954
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5955 | h5955
          · linarith only [h0, h4, h5823, h5825, h5955, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h5825, h5953, h5955, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5958 | h5958
          · linarith only [h5823, h5953, h5954, h5958, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h5825, h5953, h5958, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5961 | h5961
        · rcases m.htr 1 3 4 (by decide) (by decide) with h5962 | h5962
          · linarith only [h4, h5825, h5961, h5962, h7, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h5964 | h5964
            · rcases m.htr 1 4 5 (by decide) (by decide) with h5965 | h5965
              · rcases m.htr 2 3 4 (by decide) (by decide) with h5966 | h5966
                · linarith only [h4, h5966, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h5968 | h5968
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h5969 | h5969
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h5970 | h5970
                      · rcases h1bigk with h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c | h5971c
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h5973 | h5973
                          · rcases p5971_3 (m.d 1 2) (by simp) with h5974 | h5974
                            · linarith only [h5974, hlam, p5971_0]
                            · rcases p5971_3 (m.d 1 3) (by simp) with h5976 | h5976
                              · linarith only [h1, h5976, hlam]
                              · linarith only [h5825, h5976, hlam]
                          · linarith only [h5973, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h5980 | h5980
                          · rcases p5971_3 (m.d 1 2) (by simp) with h5981 | h5981
                            · linarith only [h0, h5981, hlam]
                            · rcases p5971_3 (m.d 1 3) (by simp) with h5983 | h5983
                              · linarith only [h5983, hlam, p5971_0]
                              · rcases p5971_3 (m.d 1 4) (by simp) with h5985 | h5985
                                · linarith only [h2, h5985, hlam]
                                · linarith only [h5962, h5985, hlam]
                          · linarith only [h5980, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h5989 | h5989
                          · rcases p5971_3 (m.d 1 2) (by simp) with h5990 | h5990
                            · linarith only [h0, h5990, hlam]
                            · rcases p5971_3 (m.d 1 3) (by simp) with h5992 | h5992
                              · linarith only [h1, h5992, hlam]
                              · rcases p5971_3 (m.d 1 4) (by simp) with h5994 | h5994
                                · linarith only [h5994, hlam, p5971_0]
                                · rcases p5971_3 (m.d 1 5) (by simp) with h5996 | h5996
                                  · linarith only [h3, h5996, hlam]
                                  · rcases h3bigk with h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c | h5998c
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5825, h5961, h5968, h5970, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5825, h5961, h5968, h5970, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h7, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      rcases p5998_3 (m.d 0 3) (by simp) with h6003 | h6003
                                      · rcases p5998_3 (m.d 1 3) (by simp) with h6004 | h6004
                                        · linarith only [h1, h6004, hlam]
                                        · linarith only [h5964, h6004, hlam]
                                      · linarith only [h6003, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h1, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5825, hlam, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5962, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5962, h5970, hc01, hc45, hlam, hphi, ht0b, ht5b, p5971_1, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h4, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h4, h7, hc13, hc34, hlam, hphi, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5966, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      rcases p5998_3 (m.d 0 3) (by simp) with h6017 | h6017
                                      · rcases p5998_3 (m.d 1 3) (by simp) with h6018 | h6018
                                        · linarith only [h5825, h6018, hlam]
                                        · linarith only [h5964, h6018, hlam]
                                      · linarith only [h5823, h6017, hlam]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h4, h5825, h5961, h5968, h5970, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      rcases p5998_3 (m.d 0 3) (by simp) with h6023 | h6023
                                      · linarith only [h6023, h7, hlam]
                                      · linarith only [h1, h6023, hlam]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5825, h5961, h5968, h5970, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5998_1]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h4, h5825, h5961, h5968, h7, hlam, p5998_2]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5823, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5964, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5968, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [h5970, hlam, p5998_0]
                                    · have p5998_0 := h5998c.1
                                      have p5998_1 := h5998c.2.1
                                      have p5998_2 := h5998c.2.2.1
                                      have p5998_3 := h5998c.2.2.2
                                      linarith only [hlam, p5998_0]
                          · linarith only [h5989, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h6035 | h6035
                          · rcases p5971_3 (m.d 1 2) (by simp) with h6036 | h6036
                            · linarith only [h0, h6036, hlam]
                            · linarith only [h5961, h6036, hlam]
                          · linarith only [h6035, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h0, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5825, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5953, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h0, h5, h5825, h5966, hc01, hc15, hlam, hphi, ht0b, ht5b, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h1, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h1, h5961, hc01, hc25, hlam, hphi, ht0b, ht5b, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5962, hlam, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h6049 | h6049
                          · rcases p5971_3 (m.d 1 2) (by simp) with h6050 | h6050
                            · linarith only [h5825, h6050, hlam]
                            · linarith only [h5961, h6050, hlam]
                          · linarith only [h3, h6049, hlam]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h2, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h2, h5961, h5968, h5970, hc01, hc45, hlam, hphi, ht0b, ht5b, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h0, h5, h5825, h5953, h5961, h5968, h5970, hc01, hc45, hlam, hphi, ht0b, ht5b, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          rcases p5971_3 (m.d 0 1) (by simp) with h6058 | h6058
                          · rcases p5971_3 (m.d 1 2) (by simp) with h6059 | h6059
                            · linarith only [h5953, h6059, hlam]
                            · linarith only [h5961, h6059, hlam]
                          · linarith only [h3, h6058, hlam]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h3, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5961, hlam, p5971_1]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5964, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [h5965, hlam, p5971_0]
                        · have p5971_0 := h5971c.1
                          have p5971_1 := h5971c.2.1
                          have p5971_2 := h5971c.2.2.1
                          have p5971_3 := h5971c.2.2.2
                          linarith only [hlam, p5971_0]
                      · linarith only [h4, h5825, h5970, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h5823, h5824, h5953, h5961, h5968, h5969, h7, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · linarith only [h5823, h5825, h5961, h5968, h7, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · linarith only [h5825, h5961, h5962, h5965, hlam]
            · linarith only [h5823, h5825, h5964, h7, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6073 | h6073
          · linarith only [h1, h5823, h6073, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6075 | h6075
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6076 | h6076
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6077 | h6077
                · linarith only [h4, h6077, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6079 | h6079
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6080 | h6080
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6081 | h6081
                      · rcases h1bigk with h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c | h6082c
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6084 | h6084
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6085 | h6085
                            · linarith only [h6085, hlam, p6082_0]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6087 | h6087
                              · linarith only [h1, h6087, hlam]
                              · linarith only [h5825, h6087, hlam]
                          · linarith only [h6084, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6091 | h6091
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6092 | h6092
                            · linarith only [h0, h6092, hlam]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6094 | h6094
                              · linarith only [h6094, hlam, p6082_0]
                              · rcases p6082_3 (m.d 1 4) (by simp) with h6096 | h6096
                                · linarith only [h2, h6096, hlam]
                                · linarith only [h6073, h6096, hlam]
                          · linarith only [h6091, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6100 | h6100
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6101 | h6101
                            · linarith only [h0, h6101, hlam]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6103 | h6103
                              · linarith only [h1, h6103, hlam]
                              · rcases p6082_3 (m.d 1 4) (by simp) with h6105 | h6105
                                · linarith only [h6105, hlam, p6082_0]
                                · rcases p6082_3 (m.d 1 5) (by simp) with h6107 | h6107
                                  · linarith only [h3, h6107, hlam]
                                  · rcases h3bigk with h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c | h6109c
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6075, h6081, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h7, hc23, hc34, hlam, hphi, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h7, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      rcases p6109_3 (m.d 0 3) (by simp) with h6114 | h6114
                                      · rcases p6109_3 (m.d 1 3) (by simp) with h6115 | h6115
                                        · linarith only [h1, h6115, hlam]
                                        · linarith only [h6075, h6115, hlam]
                                      · linarith only [h6114, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h1, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h5825, hlam, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6073, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6073, h6081, hc01, hc45, hlam, hphi, ht0b, ht5b, p6082_1, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h4, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h4, h7, hc13, hc34, hlam, hphi, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6077, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      rcases p6109_3 (m.d 0 3) (by simp) with h6128 | h6128
                                      · rcases p6109_3 (m.d 1 3) (by simp) with h6129 | h6129
                                        · linarith only [h5825, h6129, hlam]
                                        · linarith only [h6075, h6129, hlam]
                                      · linarith only [h5823, h6128, hlam]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h5823, h5961, h6, hc12, hc34, hlam, hphi, ht23, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      rcases p6109_3 (m.d 0 3) (by simp) with h6134 | h6134
                                      · linarith only [h6134, h7, hlam]
                                      · linarith only [h1, h6134, hlam]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h5825, hc12, hc34, hlam, hphi, ht23, p6109_1]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      rcases p6109_3 (m.d 0 3) (by simp) with h6139 | h6139
                                      · linarith only [h6139, h7, hlam]
                                      · linarith only [h5823, h6139, hlam]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h5823, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6075, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6079, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [h6081, hlam, p6109_0]
                                    · have p6109_0 := h6109c.1
                                      have p6109_1 := h6109c.2.1
                                      have p6109_2 := h6109c.2.2.1
                                      have p6109_3 := h6109c.2.2.2
                                      linarith only [hlam, p6109_0]
                          · linarith only [h6100, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6148 | h6148
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6149 | h6149
                            · linarith only [h0, h6149, hlam]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6151 | h6151
                              · linarith only [h1, h6151, hlam]
                              · linarith only [h6075, h6151, hlam]
                          · linarith only [h6148, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h0, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h5825, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h5953, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h5961, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h1, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h1, h7, hc12, hc34, hlam, hphi, ht23, p6082_1]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h6073, hlam, p6082_1]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h1, h5961, h7, hc12, hc34, hlam, hphi, ht23, p6082_1]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h2, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6166 | h6166
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6167 | h6167
                            · linarith only [h5953, h6167, hlam]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6169 | h6169
                              · linarith only [h6073, h6169, hlam]
                              · linarith only [h5825, h6169, hlam]
                          · linarith only [h0, h6166, hlam]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h0, h5, h5953, h6075, h6081, hc01, hc45, hlam, hphi, ht0b, ht5b, p6082_1]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          rcases p6082_3 (m.d 0 1) (by simp) with h6175 | h6175
                          · rcases p6082_3 (m.d 1 2) (by simp) with h6176 | h6176
                            · linarith only [h5953, h6176, hlam]
                            · rcases p6082_3 (m.d 1 3) (by simp) with h6178 | h6178
                              · linarith only [h6073, h6178, hlam]
                              · linarith only [h6075, h6178, hlam]
                          · linarith only [h3, h6175, hlam]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h3, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h3, h5823, h7, hc12, hc34, hlam, hphi, ht23, p6082_1]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h6075, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [h6076, hlam, p6082_0]
                        · have p6082_0 := h6082c.1
                          have p6082_1 := h6082c.2.1
                          have p6082_2 := h6082c.2.2.1
                          have p6082_3 := h6082c.2.2.2
                          linarith only [hlam, p6082_0]
                      · linarith only [h5824, h6081, h7, hlam]
                    · linarith only [h1, h5953, h6075, h6076, h6080, h7, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h5825, h6075, h6079, hlam]
              · linarith only [h6073, h6075, h6076, hlam]
            · linarith only [h5823, h6075, h7, hc13, hc34, hlam, hphi]
  · linarith only [h5823, h5824, h7, hlam]

end R2N4
