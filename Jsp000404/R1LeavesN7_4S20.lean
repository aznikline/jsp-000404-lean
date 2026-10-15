import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S19

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h14860 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 1 2 3 (by decide) (by decide) with h15662 | h15662
  · rcases m.htr 1 2 4 (by decide) (by decide) with h15663 | h15663
    · rcases m.htr 1 2 5 (by decide) (by decide) with h15664 | h15664
      · rcases m.htr 1 3 4 (by decide) (by decide) with h15665 | h15665
        · rcases m.htr 1 3 5 (by decide) (by decide) with h15666 | h15666
          · rcases m.htr 1 4 5 (by decide) (by decide) with h15667 | h15667
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15668 | h15668
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15669 | h15669
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15670 | h15670
                  · linarith only [h14857, h14860, h15670, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15672 | h15672
                    · linarith only [h14857, h14860, h15668, h15672, hlam]
                    · rcases h1bigk with h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c | h15674c
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h0, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h11385, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h13812, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        rcases p15674_3 (m.d 0 1) (by simp) with h15680 | h15680
                        · linarith only [h15680, hlam, p15674_0]
                        · rcases p15674_3 (m.d 1 2) (by simp) with h15682 | h15682
                          · rcases p15674_3 (m.d 1 3) (by simp) with h15683 | h15683
                            · linarith only [h15662, h15683, hlam]
                            · linarith only [h11385, h15683, hlam]
                          · linarith only [h15682, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, h14860, h15665, h15667, hc01, hc12, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, h14860, h15667, hc01, hc12, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h13812, hc01, hc12, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        rcases p15674_3 (m.d 0 1) (by simp) with h15691 | h15691
                        · linarith only [h15691, hlam, p15674_0]
                        · rcases p15674_3 (m.d 1 2) (by simp) with h15693 | h15693
                          · rcases p15674_3 (m.d 1 3) (by simp) with h15694 | h15694
                            · rcases p15674_3 (m.d 1 4) (by simp) with h15695 | h15695
                              · linarith only [h15665, h15695, hlam]
                              · linarith only [h12794, h15695, hlam]
                            · linarith only [h15694, hlam, p15674_0]
                          · linarith only [h0, h15693, hlam]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15662, hlam, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, h14860, h15667, hc01, hc13, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, h14860, h15662, h15667, hc01, hc12, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        rcases p15674_3 (m.d 0 1) (by simp) with h15704 | h15704
                        · linarith only [h15704, hlam, p15674_0]
                        · rcases p15674_3 (m.d 1 2) (by simp) with h15706 | h15706
                          · rcases p15674_3 (m.d 1 3) (by simp) with h15707 | h15707
                            · rcases p15674_3 (m.d 1 4) (by simp) with h15708 | h15708
                              · rcases p15674_3 (m.d 1 5) (by simp) with h15709 | h15709
                                · linarith only [h15667, h15709, hlam]
                                · linarith only [h13812, h15709, hlam]
                              · linarith only [h15708, hlam, p15674_0]
                            · linarith only [h11385, h15707, hlam]
                          · linarith only [h0, h15706, hlam]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15663, hlam, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15665, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h12794, h14860, h15667, hc01, hc14, hlam, hphi, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        rcases p15674_3 (m.d 0 1) (by simp) with h15719 | h15719
                        · linarith only [h15719, hlam, p15674_0]
                        · rcases p15674_3 (m.d 1 2) (by simp) with h15721 | h15721
                          · rcases p15674_3 (m.d 1 3) (by simp) with h15722 | h15722
                            · rcases p15674_3 (m.d 1 4) (by simp) with h15723 | h15723
                              · rcases p15674_3 (m.d 1 5) (by simp) with h15724 | h15724
                                · rcases h3bigk with h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c | h15725c
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h11385, hlam, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h0, h14856, h15669, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    rcases p15725_3 (m.d 0 3) (by simp) with h15729 | h15729
                                    · rcases p15725_3 (m.d 1 3) (by simp) with h15730 | h15730
                                      · rcases p15725_3 (m.d 2 3) (by simp) with h15731 | h15731
                                        · linarith only [h14856, h15731, hlam]
                                        · linarith only [h15668, h15731, hlam]
                                      · linarith only [h15665, h15730, hlam]
                                    · linarith only [h15729, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    rcases p15725_3 (m.d 0 3) (by simp) with h15736 | h15736
                                    · rcases p15725_3 (m.d 1 3) (by simp) with h15737 | h15737
                                      · rcases p15725_3 (m.d 2 3) (by simp) with h15738 | h15738
                                        · linarith only [h14856, h15738, hlam]
                                        · linarith only [h15669, h15738, hlam]
                                      · linarith only [h15666, h15737, hlam]
                                    · linarith only [h15736, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h11385, h15662, hc01, hc12, hlam, hphi, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15662, h15669, h15672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    rcases p15725_3 (m.d 0 3) (by simp) with h15746 | h15746
                                    · linarith only [h11385, h15746, hlam]
                                    · linarith only [h14858, h15746, hlam]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    rcases p15725_3 (m.d 0 3) (by simp) with h15749 | h15749
                                    · linarith only [h11385, h15749, hlam]
                                    · linarith only [h14859, h15749, hlam]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h14856, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15662, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h0, h14856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h0, h14856, h15672, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h14858, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15665, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15668, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15672, hlam, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h14859, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15666, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h15669, hlam, p15725_0]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [h14859, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15725_1]
                                  · have p15725_0 := h15725c.1
                                    have p15725_1 := h15725c.2.1
                                    have p15725_2 := h15725c.2.2.1
                                    have p15725_3 := h15725c.2.2.2
                                    linarith only [hlam, p15725_0]
                                · linarith only [h15724, hlam, p15674_0]
                              · linarith only [h12794, h15723, hlam]
                            · linarith only [h11385, h15722, hlam]
                          · linarith only [h0, h15721, hlam]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15664, hlam, p15674_1]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15666, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [h15667, hlam, p15674_0]
                      · have p15674_0 := h15674c.1
                        have p15674_1 := h15674c.2.1
                        have p15674_2 := h15674c.2.2.1
                        have p15674_3 := h15674c.2.2.2
                        linarith only [hlam, p15674_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15775 | h15775
                  · linarith only [h0, h14857, h14859, h14860, h15668, h15669, h15775, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15777 | h15777
                    · linarith only [h14859, h14860, h15668, h15669, h15777, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c | h15779c
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h0, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h11385, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h12794, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h13812, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        rcases p15779_3 (m.d 0 1) (by simp) with h15785 | h15785
                        · linarith only [h15785, hlam, p15779_0]
                        · rcases p15779_3 (m.d 1 2) (by simp) with h15787 | h15787
                          · rcases p15779_3 (m.d 1 3) (by simp) with h15788 | h15788
                            · linarith only [h15662, h15788, hlam]
                            · linarith only [h11385, h15788, hlam]
                          · linarith only [h15787, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h11385, hc01, hc12, hlam, hphi, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h12794, hc01, hc12, hlam, hphi, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h13812, hc01, hc12, hlam, hphi, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        rcases p15779_3 (m.d 0 1) (by simp) with h15796 | h15796
                        · linarith only [h15796, hlam, p15779_0]
                        · rcases p15779_3 (m.d 1 2) (by simp) with h15798 | h15798
                          · rcases p15779_3 (m.d 1 3) (by simp) with h15799 | h15799
                            · rcases p15779_3 (m.d 1 4) (by simp) with h15800 | h15800
                              · linarith only [h15665, h15800, hlam]
                              · linarith only [h12794, h15800, hlam]
                            · linarith only [h15799, hlam, p15779_0]
                          · linarith only [h0, h15798, hlam]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15662, hlam, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h14859, h14860, h15667, h15668, h15669, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h14859, h14860, h15662, h15667, h15668, h15669, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        rcases p15779_3 (m.d 0 1) (by simp) with h15809 | h15809
                        · linarith only [h15809, hlam, p15779_0]
                        · rcases p15779_3 (m.d 1 2) (by simp) with h15811 | h15811
                          · rcases p15779_3 (m.d 1 3) (by simp) with h15812 | h15812
                            · rcases p15779_3 (m.d 1 4) (by simp) with h15813 | h15813
                              · rcases p15779_3 (m.d 1 5) (by simp) with h15814 | h15814
                                · linarith only [h15667, h15814, hlam]
                                · linarith only [h13812, h15814, hlam]
                              · linarith only [h15813, hlam, p15779_0]
                            · linarith only [h11385, h15812, hlam]
                          · linarith only [h0, h15811, hlam]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15663, hlam, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15665, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h14859, h14860, h15667, h15668, h15669, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        rcases p15779_3 (m.d 0 1) (by simp) with h15824 | h15824
                        · linarith only [h15824, hlam, p15779_0]
                        · rcases p15779_3 (m.d 1 2) (by simp) with h15826 | h15826
                          · rcases p15779_3 (m.d 1 3) (by simp) with h15827 | h15827
                            · rcases p15779_3 (m.d 1 4) (by simp) with h15828 | h15828
                              · rcases p15779_3 (m.d 1 5) (by simp) with h15829 | h15829
                                · rcases h3bigk with h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c | h15830c
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h11385, hlam, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15668, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    rcases p15830_3 (m.d 0 3) (by simp) with h15834 | h15834
                                    · rcases p15830_3 (m.d 1 3) (by simp) with h15835 | h15835
                                      · rcases p15830_3 (m.d 2 3) (by simp) with h15836 | h15836
                                        · linarith only [h14856, h15836, hlam]
                                        · linarith only [h15668, h15836, hlam]
                                      · linarith only [h15665, h15835, hlam]
                                    · linarith only [h15834, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h11385, h15662, h15668, h15669, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h11385, h15662, hc01, hc12, hlam, hphi, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15662, h15668, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    rcases p15830_3 (m.d 0 3) (by simp) with h15845 | h15845
                                    · linarith only [h11385, h15845, hlam]
                                    · linarith only [h14858, h15845, hlam]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15662, h15668, h15669, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14856, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15662, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14859, h15669, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15669, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14858, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15665, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15668, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15777, hlam, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14859, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h15666, hlam, p15830_0]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14859, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [h14859, h14860, h15662, h15665, h15667, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15830_1]
                                  · have p15830_0 := h15830c.1
                                    have p15830_1 := h15830c.2.1
                                    have p15830_2 := h15830c.2.2.1
                                    have p15830_3 := h15830c.2.2.2
                                    linarith only [hlam, p15830_0]
                                · linarith only [h15829, hlam, p15779_0]
                              · linarith only [h12794, h15828, hlam]
                            · linarith only [h11385, h15827, hlam]
                          · linarith only [h0, h15826, hlam]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15664, hlam, p15779_1]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15666, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [h15667, hlam, p15779_0]
                      · have p15779_0 := h15779c.1
                        have p15779_1 := h15779c.2.1
                        have p15779_2 := h15779c.2.2.1
                        have p15779_3 := h15779c.2.2.2
                        linarith only [hlam, p15779_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15872 | h15872
                · linarith only [h14858, h14860, h15662, h15665, h15667, h15668, h15872, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15874 | h15874
                  · linarith only [h0, h14857, h14858, h14860, h15668, h15874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15876 | h15876
                    · linarith only [h14858, h14860, h15876, hlam]
                    · rcases h1bigk with h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c | h15878c
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h0, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h11385, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h12794, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h13812, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        rcases p15878_3 (m.d 0 1) (by simp) with h15884 | h15884
                        · linarith only [h15884, hlam, p15878_0]
                        · rcases p15878_3 (m.d 1 2) (by simp) with h15886 | h15886
                          · rcases p15878_3 (m.d 1 3) (by simp) with h15887 | h15887
                            · linarith only [h15662, h15887, hlam]
                            · linarith only [h11385, h15887, hlam]
                          · linarith only [h15886, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h11385, hc01, hc12, hlam, hphi, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h12794, hc01, hc12, hlam, hphi, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h13812, hc01, hc12, hlam, hphi, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        rcases p15878_3 (m.d 0 1) (by simp) with h15895 | h15895
                        · linarith only [h15895, hlam, p15878_0]
                        · rcases p15878_3 (m.d 1 2) (by simp) with h15897 | h15897
                          · rcases p15878_3 (m.d 1 3) (by simp) with h15898 | h15898
                            · rcases p15878_3 (m.d 1 4) (by simp) with h15899 | h15899
                              · linarith only [h15665, h15899, hlam]
                              · linarith only [h12794, h15899, hlam]
                            · linarith only [h15898, hlam, p15878_0]
                          · linarith only [h0, h15897, hlam]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15662, hlam, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h14858, h14860, h15667, h15668, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h14858, h14860, h15662, h15667, h15668, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        rcases p15878_3 (m.d 0 1) (by simp) with h15908 | h15908
                        · linarith only [h15908, hlam, p15878_0]
                        · rcases p15878_3 (m.d 1 2) (by simp) with h15910 | h15910
                          · rcases p15878_3 (m.d 1 3) (by simp) with h15911 | h15911
                            · rcases p15878_3 (m.d 1 4) (by simp) with h15912 | h15912
                              · rcases p15878_3 (m.d 1 5) (by simp) with h15913 | h15913
                                · linarith only [h15667, h15913, hlam]
                                · linarith only [h13812, h15913, hlam]
                              · linarith only [h15912, hlam, p15878_0]
                            · linarith only [h11385, h15911, hlam]
                          · linarith only [h0, h15910, hlam]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15663, hlam, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15665, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h14858, h14860, h15667, h15668, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        rcases p15878_3 (m.d 0 1) (by simp) with h15923 | h15923
                        · linarith only [h15923, hlam, p15878_0]
                        · rcases p15878_3 (m.d 1 2) (by simp) with h15925 | h15925
                          · rcases p15878_3 (m.d 1 3) (by simp) with h15926 | h15926
                            · rcases p15878_3 (m.d 1 4) (by simp) with h15927 | h15927
                              · rcases p15878_3 (m.d 1 5) (by simp) with h15928 | h15928
                                · rcases h3bigk with h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c | h15929c
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h11385, hlam, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    rcases p15929_3 (m.d 0 3) (by simp) with h15932 | h15932
                                    · rcases p15929_3 (m.d 1 3) (by simp) with h15933 | h15933
                                      · rcases p15929_3 (m.d 2 3) (by simp) with h15934 | h15934
                                        · linarith only [h14856, h15934, hlam]
                                        · rcases p15929_3 (m.d 3 4) (by simp) with h15936 | h15936
                                          · linarith only [h14858, h15936, hlam]
                                          · linarith only [h15668, h15936, hlam]
                                      · linarith only [h15662, h15933, hlam]
                                    · linarith only [h14856, h15932, hlam]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15668, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h11385, h15662, h15668, h15876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h11385, h15662, hc01, hc12, hlam, hphi, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    rcases p15929_3 (m.d 0 3) (by simp) with h15945 | h15945
                                    · linarith only [h11385, h15945, hlam]
                                    · linarith only [h14856, h15945, hlam]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15662, h15668, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15662, h15668, h15876, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14856, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15662, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15668, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15872, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14858, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15665, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14859, h15876, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15876, hlam, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14859, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h15666, hlam, p15929_0]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14859, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [h14859, h14860, h15662, h15665, h15667, h15668, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p15929_1]
                                  · have p15929_0 := h15929c.1
                                    have p15929_1 := h15929c.2.1
                                    have p15929_2 := h15929c.2.2.1
                                    have p15929_3 := h15929c.2.2.2
                                    linarith only [hlam, p15929_0]
                                · linarith only [h15928, hlam, p15878_0]
                              · linarith only [h12794, h15927, hlam]
                            · linarith only [h11385, h15926, hlam]
                          · linarith only [h0, h15925, hlam]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15664, hlam, p15878_1]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15666, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [h15667, hlam, p15878_0]
                      · have p15878_0 := h15878c.1
                        have p15878_1 := h15878c.2.1
                        have p15878_2 := h15878c.2.2.1
                        have p15878_3 := h15878c.2.2.2
                        linarith only [hlam, p15878_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h15973 | h15973
              · rcases m.htr 2 3 5 (by decide) (by decide) with h15974 | h15974
                · rcases m.htr 2 4 5 (by decide) (by decide) with h15975 | h15975
                  · linarith only [h12794, h15667, h15975, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h15977 | h15977
                    · linarith only [h12794, h15667, h15973, h15977, hc01, hc23, hlam, hphi, ht12]
                    · rcases h1bigk with h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c | h15979c
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h0, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h11385, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h12794, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h13812, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        rcases p15979_3 (m.d 0 1) (by simp) with h15985 | h15985
                        · linarith only [h15985, hlam, p15979_0]
                        · rcases p15979_3 (m.d 1 2) (by simp) with h15987 | h15987
                          · rcases p15979_3 (m.d 1 3) (by simp) with h15988 | h15988
                            · linarith only [h15662, h15988, hlam]
                            · linarith only [h11385, h15988, hlam]
                          · linarith only [h15987, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h11385, hc01, hc12, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h12794, hc01, hc12, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h13812, hc01, hc12, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        rcases p15979_3 (m.d 0 1) (by simp) with h15996 | h15996
                        · linarith only [h15996, hlam, p15979_0]
                        · rcases p15979_3 (m.d 1 2) (by simp) with h15998 | h15998
                          · rcases p15979_3 (m.d 1 3) (by simp) with h15999 | h15999
                            · rcases p15979_3 (m.d 1 4) (by simp) with h16000 | h16000
                              · linarith only [h15665, h16000, hlam]
                              · linarith only [h12794, h16000, hlam]
                            · linarith only [h15999, hlam, p15979_0]
                          · linarith only [h0, h15998, hlam]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15662, hlam, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h12794, hc01, hc13, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h13812, h15662, hc01, hc12, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15663, hlam, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15665, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15667, hlam, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        rcases p15979_3 (m.d 0 1) (by simp) with h16014 | h16014
                        · linarith only [h16014, hlam, p15979_0]
                        · rcases p15979_3 (m.d 1 2) (by simp) with h16016 | h16016
                          · rcases p15979_3 (m.d 1 3) (by simp) with h16017 | h16017
                            · rcases p15979_3 (m.d 1 4) (by simp) with h16018 | h16018
                              · linarith only [h15667, h16018, hlam]
                              · linarith only [h12794, h16018, hlam]
                            · linarith only [h11385, h16017, hlam]
                          · linarith only [h0, h16016, hlam]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15664, hlam, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h15666, hlam, p15979_0]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [h12794, hc01, hc15, hlam, hphi, p15979_1]
                      · have p15979_0 := h15979c.1
                        have p15979_1 := h15979c.2.1
                        have p15979_2 := h15979c.2.2.1
                        have p15979_3 := h15979c.2.2.2
                        linarith only [hlam, p15979_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16027 | h16027
                  · linarith only [h11385, h13812, h14859, h15662, h15667, h15973, h15974, h16027, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16029 | h16029
                    · linarith only [h11385, h13812, h14858, h15662, h15667, h16029, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c | h16031c
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h0, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h11385, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h12794, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h13812, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        rcases p16031_3 (m.d 0 1) (by simp) with h16037 | h16037
                        · linarith only [h16037, hlam, p16031_0]
                        · rcases p16031_3 (m.d 1 2) (by simp) with h16039 | h16039
                          · rcases p16031_3 (m.d 1 3) (by simp) with h16040 | h16040
                            · linarith only [h15662, h16040, hlam]
                            · linarith only [h11385, h16040, hlam]
                          · linarith only [h16039, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h11385, hc01, hc12, hlam, hphi, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h12794, hc01, hc12, hlam, hphi, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h13812, h14859, h15973, h15974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        rcases p16031_3 (m.d 0 1) (by simp) with h16048 | h16048
                        · linarith only [h16048, hlam, p16031_0]
                        · rcases p16031_3 (m.d 1 2) (by simp) with h16050 | h16050
                          · rcases p16031_3 (m.d 1 3) (by simp) with h16051 | h16051
                            · rcases p16031_3 (m.d 1 4) (by simp) with h16052 | h16052
                              · linarith only [h15665, h16052, hlam]
                              · linarith only [h12794, h16052, hlam]
                            · linarith only [h16051, hlam, p16031_0]
                          · linarith only [h0, h16050, hlam]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15662, hlam, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h12794, hc01, hc13, hlam, hphi, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h13812, h14859, h15662, h15973, h15974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15663, hlam, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15665, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15667, hlam, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        rcases p16031_3 (m.d 0 1) (by simp) with h16066 | h16066
                        · linarith only [h16066, hlam, p16031_0]
                        · rcases p16031_3 (m.d 1 2) (by simp) with h16068 | h16068
                          · rcases p16031_3 (m.d 1 3) (by simp) with h16069 | h16069
                            · rcases p16031_3 (m.d 1 4) (by simp) with h16070 | h16070
                              · linarith only [h15667, h16070, hlam]
                              · linarith only [h12794, h16070, hlam]
                            · linarith only [h11385, h16069, hlam]
                          · linarith only [h0, h16068, hlam]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15664, hlam, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h15666, hlam, p16031_0]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [h12794, hc01, hc15, hlam, hphi, p16031_1]
                      · have p16031_0 := h16031c.1
                        have p16031_1 := h16031c.2.1
                        have p16031_2 := h16031c.2.2.1
                        have p16031_3 := h16031c.2.2.2
                        linarith only [hlam, p16031_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16079 | h16079
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16080 | h16080
                  · linarith only [h12794, h14858, h15667, h15973, h16079, h16080, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h15973, h16079, h16080, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16083 | h16083
                  · linarith only [h12794, h15667, h16083, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16085 | h16085
                    · linarith only [h12794, h15667, h16085, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h1bigk with h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c | h16087c
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h0, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h11385, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h12794, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h13812, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        rcases p16087_3 (m.d 0 1) (by simp) with h16093 | h16093
                        · linarith only [h16093, hlam, p16087_0]
                        · rcases p16087_3 (m.d 1 2) (by simp) with h16095 | h16095
                          · rcases p16087_3 (m.d 1 3) (by simp) with h16096 | h16096
                            · linarith only [h15662, h16096, hlam]
                            · linarith only [h11385, h16096, hlam]
                          · linarith only [h16095, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h11385, hc01, hc12, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h12794, hc01, hc12, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h13812, hc01, hc12, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        rcases p16087_3 (m.d 0 1) (by simp) with h16104 | h16104
                        · linarith only [h16104, hlam, p16087_0]
                        · rcases p16087_3 (m.d 1 2) (by simp) with h16106 | h16106
                          · rcases p16087_3 (m.d 1 3) (by simp) with h16107 | h16107
                            · rcases p16087_3 (m.d 1 4) (by simp) with h16108 | h16108
                              · linarith only [h15665, h16108, hlam]
                              · linarith only [h12794, h16108, hlam]
                            · linarith only [h16107, hlam, p16087_0]
                          · linarith only [h0, h16106, hlam]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15662, hlam, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h12794, hc01, hc13, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h12794, h15662, h15667, hc01, hc12, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15663, hlam, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15665, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15667, hlam, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        rcases p16087_3 (m.d 0 1) (by simp) with h16122 | h16122
                        · linarith only [h16122, hlam, p16087_0]
                        · rcases p16087_3 (m.d 1 2) (by simp) with h16124 | h16124
                          · rcases p16087_3 (m.d 1 3) (by simp) with h16125 | h16125
                            · rcases p16087_3 (m.d 1 4) (by simp) with h16126 | h16126
                              · linarith only [h15667, h16126, hlam]
                              · linarith only [h12794, h16126, hlam]
                            · linarith only [h11385, h16125, hlam]
                          · linarith only [h0, h16124, hlam]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15664, hlam, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h15666, hlam, p16087_0]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [h12794, hc01, hc15, hlam, hphi, p16087_1]
                      · have p16087_0 := h16087c.1
                        have p16087_1 := h16087c.2.1
                        have p16087_2 := h16087c.2.2.1
                        have p16087_3 := h16087c.2.2.2
                        linarith only [hlam, p16087_0]
          · linarith only [h11385, h14859, h15666, hlam]
        · linarith only [h11385, h14858, h15665, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h16137 | h16137
        · rcases m.htr 1 3 5 (by decide) (by decide) with h16138 | h16138
          · linarith only [h15662, h15664, h16138, hlam]
          · linarith only [h0, h12794, h14856, h14859, h16137, h16138, hc01, hc12, hlam, hphi]
        · linarith only [h11385, h14858, h16137, hlam]
    · linarith only [h0, h14857, h15663, hlam]
  · linarith only [h0, h14856, h15662, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 4 5 (by decide) (by decide) with h14860 | h14860
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859 h14860

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h14859 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 4 5 (by decide) (by decide) with h16144 | h16144
  · linarith only [h14858, h14859, h16144, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h16146 | h16146
    · rcases m.htr 1 2 4 (by decide) (by decide) with h16147 | h16147
      · rcases m.htr 1 2 5 (by decide) (by decide) with h16148 | h16148
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16149 | h16149
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16150 | h16150
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16151 | h16151
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16152 | h16152
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16153 | h16153
                  · linarith only [h0, h11385, h14856, h14859, h16153, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16155 | h16155
                    · linarith only [h14857, h16144, h16155, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16157 | h16157
                      · linarith only [h12794, h14856, h14859, h16144, h16150, h16152, h16157, hc01, hc13, hlam, hphi]
                      · rcases h1bigk with h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c | h16159c
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h0, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h11385, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h12794, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h13812, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          rcases p16159_3 (m.d 0 1) (by simp) with h16165 | h16165
                          · linarith only [h16165, hlam, p16159_0]
                          · rcases p16159_3 (m.d 1 2) (by simp) with h16167 | h16167
                            · rcases p16159_3 (m.d 1 3) (by simp) with h16168 | h16168
                              · linarith only [h16146, h16168, hlam]
                              · linarith only [h11385, h16168, hlam]
                            · linarith only [h16167, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14859, h16149, h16151, h16157, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14856, h14859, h16151, h16152, h16157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14856, h14859, h16151, h16152, h16157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          rcases p16159_3 (m.d 0 1) (by simp) with h16176 | h16176
                          · linarith only [h16176, hlam, p16159_0]
                          · rcases p16159_3 (m.d 1 2) (by simp) with h16178 | h16178
                            · rcases p16159_3 (m.d 1 3) (by simp) with h16179 | h16179
                              · rcases p16159_3 (m.d 1 4) (by simp) with h16180 | h16180
                                · linarith only [h16149, h16180, hlam]
                                · linarith only [h12794, h16180, hlam]
                              · linarith only [h16179, hlam, p16159_0]
                            · linarith only [h0, h16178, hlam]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16146, hlam, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14856, h14859, h16151, h16152, h16157, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14856, h14859, h16146, h16151, h16152, h16157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          rcases p16159_3 (m.d 0 1) (by simp) with h16189 | h16189
                          · linarith only [h16189, hlam, p16159_0]
                          · rcases p16159_3 (m.d 1 2) (by simp) with h16191 | h16191
                            · rcases p16159_3 (m.d 1 3) (by simp) with h16192 | h16192
                              · rcases p16159_3 (m.d 1 4) (by simp) with h16193 | h16193
                                · rcases p16159_3 (m.d 1 5) (by simp) with h16194 | h16194
                                  · linarith only [h16151, h16194, hlam]
                                  · linarith only [h13812, h16194, hlam]
                                · linarith only [h16193, hlam, p16159_0]
                              · linarith only [h11385, h16192, hlam]
                            · linarith only [h0, h16191, hlam]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16147, hlam, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16149, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h14856, h14859, h16151, h16152, h16157, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          rcases p16159_3 (m.d 0 1) (by simp) with h16204 | h16204
                          · linarith only [h16204, hlam, p16159_0]
                          · rcases p16159_3 (m.d 1 2) (by simp) with h16206 | h16206
                            · rcases p16159_3 (m.d 1 3) (by simp) with h16207 | h16207
                              · rcases p16159_3 (m.d 1 4) (by simp) with h16208 | h16208
                                · rcases p16159_3 (m.d 1 5) (by simp) with h16209 | h16209
                                  · rcases h3bigk with h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c | h16210c
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h11385, hlam, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16152, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h14859, h16157, hc34, hc45, hlam, hphi, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h14859, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h11385, h16146, hc01, hc12, hlam, hphi, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16146, h16152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      rcases p16210_3 (m.d 0 3) (by simp) with h16219 | h16219
                                      · linarith only [h11385, h16219, hlam]
                                      · linarith only [h14858, h16219, hlam]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h13812, h14859, h16146, hc01, hc12, hlam, hphi, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h14856, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16146, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h0, h14856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16153, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h14858, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16149, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16152, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16157, hlam, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hc03, hc35, hlam, hphi, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16150, hlam, p16210_0]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16146, h16150, h16152, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [h16146, h16149, h16151, h16157, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16210_1]
                                    · have p16210_0 := h16210c.1
                                      have p16210_1 := h16210c.2.1
                                      have p16210_2 := h16210c.2.2.1
                                      have p16210_3 := h16210c.2.2.2
                                      linarith only [hlam, p16210_0]
                                  · linarith only [h16209, hlam, p16159_0]
                                · linarith only [h12794, h16208, hlam]
                              · linarith only [h11385, h16207, hlam]
                            · linarith only [h0, h16206, hlam]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16148, hlam, p16159_1]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16150, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [h16151, hlam, p16159_0]
                        · have p16159_0 := h16159c.1
                          have p16159_1 := h16159c.2.1
                          have p16159_2 := h16159c.2.2.1
                          have p16159_3 := h16159c.2.2.2
                          linarith only [hlam, p16159_0]
                · linarith only [h14858, h14859, h16152, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16247 | h16247
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16248 | h16248
                  · linarith only [h0, h11385, h14856, h14859, h16248, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16250 | h16250
                    · linarith only [h12794, h16151, h16250, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16252 | h16252
                      · linarith only [h12794, h14856, h16151, h16247, h16252, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c | h16254c
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h0, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h11385, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h12794, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h13812, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          rcases p16254_3 (m.d 0 1) (by simp) with h16260 | h16260
                          · linarith only [h16260, hlam, p16254_0]
                          · rcases p16254_3 (m.d 1 2) (by simp) with h16262 | h16262
                            · rcases p16254_3 (m.d 1 3) (by simp) with h16263 | h16263
                              · linarith only [h16146, h16263, hlam]
                              · linarith only [h11385, h16263, hlam]
                            · linarith only [h16262, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h14859, h16150, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h12794, hc01, hc12, hlam, hphi, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h13812, hc01, hc12, hlam, hphi, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          rcases p16254_3 (m.d 0 1) (by simp) with h16271 | h16271
                          · linarith only [h16271, hlam, p16254_0]
                          · rcases p16254_3 (m.d 1 2) (by simp) with h16273 | h16273
                            · rcases p16254_3 (m.d 1 3) (by simp) with h16274 | h16274
                              · rcases p16254_3 (m.d 1 4) (by simp) with h16275 | h16275
                                · linarith only [h16149, h16275, hlam]
                                · linarith only [h12794, h16275, hlam]
                              · linarith only [h16274, hlam, p16254_0]
                            · linarith only [h0, h16273, hlam]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16146, hlam, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h12794, hc01, hc13, hlam, hphi, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h14856, h14859, h16146, h16150, h16247, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16151, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16147, hlam, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16149, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16151, hlam, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          rcases p16254_3 (m.d 0 1) (by simp) with h16289 | h16289
                          · linarith only [h16289, hlam, p16254_0]
                          · rcases p16254_3 (m.d 1 2) (by simp) with h16291 | h16291
                            · rcases p16254_3 (m.d 1 3) (by simp) with h16292 | h16292
                              · rcases p16254_3 (m.d 1 4) (by simp) with h16293 | h16293
                                · linarith only [h16151, h16293, hlam]
                                · linarith only [h12794, h16293, hlam]
                              · linarith only [h11385, h16292, hlam]
                            · linarith only [h0, h16291, hlam]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16148, hlam, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h16150, hlam, p16254_0]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [h12794, hc01, hc15, hlam, hphi, p16254_1]
                        · have p16254_0 := h16254c.1
                          have p16254_1 := h16254c.2.1
                          have p16254_2 := h16254c.2.2.1
                          have p16254_3 := h16254c.2.2.2
                          linarith only [hlam, p16254_0]
                · linarith only [h14858, h14859, h16247, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16303 | h16303
              · linarith only [h12794, h16144, h16149, h16150, h16303, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16305 | h16305
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16306 | h16306
                  · linarith only [h11385, h16150, h16306, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16308 | h16308
                    · linarith only [h12794, h16303, h16308, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16310 | h16310
                      · linarith only [h12794, h14856, h16303, h16305, h16310, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · rcases h1bigk with h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c | h16312c
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h0, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h11385, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h12794, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h13812, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          rcases p16312_3 (m.d 0 1) (by simp) with h16318 | h16318
                          · linarith only [h16318, hlam, p16312_0]
                          · rcases p16312_3 (m.d 1 2) (by simp) with h16320 | h16320
                            · rcases p16312_3 (m.d 1 3) (by simp) with h16321 | h16321
                              · linarith only [h16146, h16321, hlam]
                              · linarith only [h11385, h16321, hlam]
                            · linarith only [h16320, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h11385, hc01, hc12, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h12794, hc01, hc12, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h13812, hc01, hc12, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16150, h16310, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16146, hlam, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h12794, hc01, hc13, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16150, hlam, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16149, h16150, h16310, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16147, hlam, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16149, hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [hlam, p16312_0]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16303, hlam, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          rcases p16312_3 (m.d 0 1) (by simp) with h16339 | h16339
                          · linarith only [h16339, hlam, p16312_0]
                          · rcases p16312_3 (m.d 1 2) (by simp) with h16341 | h16341
                            · rcases p16312_3 (m.d 1 3) (by simp) with h16342 | h16342
                              · linarith only [h16150, h16342, hlam]
                              · linarith only [h11385, h16342, hlam]
                            · linarith only [h0, h16341, hlam]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h16148, hlam, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h11385, hc01, hc15, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [h12794, hc01, hc15, hlam, hphi, p16312_1]
                        · have p16312_0 := h16312c.1
                          have p16312_1 := h16312c.2.1
                          have p16312_2 := h16312c.2.2.1
                          have p16312_3 := h16312c.2.2.2
                          linarith only [hlam, p16312_0]
                · linarith only [h14858, h14859, h16305, hc23, hc35, hlam, hphi]
          · linarith only [h11385, h14858, h16149, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h16352 | h16352
          · rcases m.htr 1 3 5 (by decide) (by decide) with h16353 | h16353
            · linarith only [h14858, h14859, h16146, h16148, h16353, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h16355 | h16355
              · linarith only [h12794, h16144, h16147, h16148, h16355, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h16357 | h16357
                · rcases m.htr 2 3 5 (by decide) (by decide) with h16358 | h16358
                  · linarith only [h11385, h16353, h16358, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16360 | h16360
                    · linarith only [h12794, h16355, h16360, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h14856, h16148, h16357, h16360, hc34, hc45, hlam, hphi]
                · linarith only [h14858, h14859, h16357, hc23, hc35, hlam, hphi]
          · linarith only [h11385, h14858, h16352, hlam]
      · linarith only [h0, h14857, h16147, hlam]
    · linarith only [h0, h14856, h16146, hlam]

set_option maxHeartbeats 5010000 in
set_option maxHeartbeats 5010000 in
theorem r1l7_11_23_L_I_H_I_s15_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg14856 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14857 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14858 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h0 := hg0
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  have h14856 := hg14856
  rcases m.htr 0 3 5 (by decide) (by decide) with h14859 | h14859
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x0 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859
  · exact r1l7_11_23_L_I_H_I_s15_x0_x0_x1 m hb1 hb3 hg0 hg11385 hg12794 hg13812 hg14856 h14857 h14858 h14859

end R2N4
