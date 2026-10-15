import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S26
import Jsp000404.R1LeavesN7_1S27

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h16013 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h16176 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 1 2 3 (by decide) (by decide) with h16741 | h16741
  · rcases m.htr 1 2 4 (by decide) (by decide) with h16742 | h16742
    · rcases m.htr 1 2 5 (by decide) (by decide) with h16743 | h16743
      · rcases m.htr 1 3 4 (by decide) (by decide) with h16744 | h16744
        · linarith only [h15532, h15538, h16744, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h16746 | h16746
          · linarith only [h15532, h16013, h16746, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h16748 | h16748
            · linarith only [h0, h15533, h16176, h16748, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h16750 | h16750
              · linarith only [h15532, h15538, h16741, h16750, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h16752 | h16752
                · linarith only [h15532, h16013, h16741, h16752, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h16754 | h16754
                  · linarith only [h15533, h16176, h16742, h16754, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h16756 | h16756
                    · rcases h0bigk with h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c | h16757c
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h0, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16760 | h16760
                        · rcases p16757_3 (m.d 0 2) (by simp) with h16761 | h16761
                          · rcases p16757_3 (m.d 0 3) (by simp) with h16762 | h16762
                            · linarith only [h15532, h16762, hlam]
                            · rcases p16757_3 (m.d 0 4) (by simp) with h16764 | h16764
                              · linarith only [h15533, h16764, hlam]
                              · linarith only [h15538, h16764, hlam]
                          · linarith only [h15535, h16761, hlam]
                        · linarith only [h15532, h16760, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16769 | h16769
                        · rcases p16757_3 (m.d 0 2) (by simp) with h16770 | h16770
                          · rcases p16757_3 (m.d 0 3) (by simp) with h16771 | h16771
                            · linarith only [h15532, h16771, hlam]
                            · rcases p16757_3 (m.d 0 4) (by simp) with h16773 | h16773
                              · linarith only [h15533, h16773, hlam]
                              · rcases p16757_3 (m.d 0 5) (by simp) with h16775 | h16775
                                · linarith only [h15534, h16775, hlam]
                                · linarith only [h16176, h16775, hlam]
                          · linarith only [h15536, h16770, hlam]
                        · linarith only [h15533, h16769, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16780 | h16780
                        · rcases p16757_3 (m.d 0 2) (by simp) with h16781 | h16781
                          · rcases p16757_3 (m.d 0 3) (by simp) with h16782 | h16782
                            · linarith only [h15532, h16782, hlam]
                            · rcases p16757_3 (m.d 0 4) (by simp) with h16784 | h16784
                              · linarith only [h15533, h16784, hlam]
                              · rcases p16757_3 (m.d 0 5) (by simp) with h16786 | h16786
                                · linarith only [h15534, h16786, hlam]
                                · rcases h2bigk with h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c | h16788c
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, hlam, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    rcases p16788_3 (m.d 0 2) (by simp) with h16791 | h16791
                                    · rcases p16788_3 (m.d 1 2) (by simp) with h16792 | h16792
                                      · rcases p16788_3 (m.d 2 3) (by simp) with h16793 | h16793
                                        · linarith only [h16793, hlam, p16788_0]
                                        · rcases p16788_3 (m.d 2 4) (by simp) with h16795 | h16795
                                          · linarith only [h15536, h16795, hlam]
                                          · linarith only [h16750, h16795, hlam]
                                      · linarith only [h16741, h16792, hlam]
                                    · linarith only [h16791, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    rcases p16788_3 (m.d 0 2) (by simp) with h16800 | h16800
                                    · rcases p16788_3 (m.d 1 2) (by simp) with h16801 | h16801
                                      · rcases p16788_3 (m.d 2 3) (by simp) with h16802 | h16802
                                        · linarith only [h15535, h16802, hlam]
                                        · rcases p16788_3 (m.d 2 4) (by simp) with h16804 | h16804
                                          · linarith only [h16804, hlam, p16788_0]
                                          · rcases p16788_3 (m.d 2 5) (by simp) with h16806 | h16806
                                            · linarith only [h15537, h16806, hlam]
                                            · linarith only [h16754, h16806, hlam]
                                      · linarith only [h16742, h16801, hlam]
                                    · linarith only [h16800, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    rcases p16788_3 (m.d 0 2) (by simp) with h16811 | h16811
                                    · rcases p16788_3 (m.d 1 2) (by simp) with h16812 | h16812
                                      · rcases p16788_3 (m.d 2 3) (by simp) with h16813 | h16813
                                        · linarith only [h15535, h16813, hlam]
                                        · rcases p16788_3 (m.d 2 4) (by simp) with h16815 | h16815
                                          · linarith only [h15536, h16815, hlam]
                                          · rcases p16788_3 (m.d 2 5) (by simp) with h16817 | h16817
                                            · linarith only [h16817, hlam, p16788_0]
                                            · rcases h3bigk with h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c | h16819c
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h15538, h16176, h16741, h16756, hc23, hc34, hlam, hphi, p16819_1]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h0, h15538, h16176, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16819_1]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h15538, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16013, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h15532, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h0, h15532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16819_1]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16744, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16746, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h15535, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16741, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16750, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16752, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16835 | h16835
                                                · linarith only [h16835, hlam, p16819_0]
                                                · rcases p16819_3 (m.d 1 3) (by simp) with h16837 | h16837
                                                  · linarith only [h16744, h16837, hlam]
                                                  · rcases p16819_3 (m.d 2 3) (by simp) with h16839 | h16839
                                                    · linarith only [h16750, h16839, hlam]
                                                    · rcases p16819_3 (m.d 3 4) (by simp) with h16841 | h16841
                                                      · rcases p16819_3 (m.d 3 5) (by simp) with h16842 | h16842
                                                        · linarith only [h16756, h16842, hlam]
                                                        · linarith only [h16013, h16842, hlam]
                                                      · linarith only [h16841, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16846 | h16846
                                                · linarith only [h15538, h16846, hlam]
                                                · linarith only [h15532, h16846, hlam]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16849 | h16849
                                                · linarith only [h15538, h16849, hlam]
                                                · linarith only [h15535, h16849, hlam]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16013, hc03, hc34, hlam, hphi, p16819_1]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16854 | h16854
                                                · linarith only [h16854, hlam, p16819_0]
                                                · rcases p16819_3 (m.d 1 3) (by simp) with h16856 | h16856
                                                  · linarith only [h16746, h16856, hlam]
                                                  · rcases p16819_3 (m.d 2 3) (by simp) with h16858 | h16858
                                                    · linarith only [h16752, h16858, hlam]
                                                    · rcases p16819_3 (m.d 3 4) (by simp) with h16860 | h16860
                                                      · rcases p16819_3 (m.d 3 5) (by simp) with h16861 | h16861
                                                        · rcases h5bigk with h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c | h16862c
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h0, h16748, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p16757_1, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h0, h16750, h16754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16013, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16176, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h15534, hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h0, h15534, h16750, h16754, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16746, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16748, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h15537, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16743, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16752, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16754, hlam, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h15533, h16176, h16742, h16750, hc23, hc35, hlam, hphi, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16743, h16750, h16754, hc23, hc35, hlam, hphi, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16750, h16754, hc23, hc35, hlam, hphi, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h15533, h16176, h16742, h16750, h16756, hc23, hc34, hlam, hphi, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h15533, h16176, h16742, h16750, hc23, hc45, hlam, hphi, ht34, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16743, h16750, h16754, hc23, hc45, hlam, hphi, ht34, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16750, h16754, hc23, hc45, hlam, hphi, ht34, p16862_1]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [h16756, hlam, p16862_0]
                                                          · have p16862_0 := h16862c.1
                                                            have p16862_1 := h16862c.2.1
                                                            have p16862_2 := h16862c.2.2.1
                                                            have p16862_3 := h16862c.2.2.2
                                                            linarith only [hlam, p16862_0]
                                                        · linarith only [h16861, hlam, p16819_0]
                                                      · linarith only [h15538, h16860, hlam]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16890 | h16890
                                                · linarith only [h16013, h16890, hlam]
                                                · linarith only [h15532, h16890, hlam]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                rcases p16819_3 (m.d 0 3) (by simp) with h16893 | h16893
                                                · linarith only [h16013, h16893, hlam]
                                                · linarith only [h15535, h16893, hlam]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [h16756, hlam, p16819_0]
                                              · have p16819_0 := h16819c.1
                                                have p16819_1 := h16819c.2.1
                                                have p16819_2 := h16819c.2.2.1
                                                have p16819_3 := h16819c.2.2.2
                                                linarith only [hlam, p16819_0]
                                      · linarith only [h16743, h16812, hlam]
                                    · linarith only [h16811, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15533, h16176, h16742, h16750, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15533, h16176, h16742, h16750, hlam, p16757_1, p16788_2]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15533, h16176, h16742, hlam, p16757_1, p16788_2]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15534, h16743, hlam, p16757_1, p16788_2]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h15535, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16741, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16750, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16752, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h15536, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16742, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h15533, h16176, h16742, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16757_1, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16754, hlam, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h15537, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h16743, hlam, p16788_0]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16757_1, p16788_1]
                                  · have p16788_0 := h16788c.1
                                    have p16788_1 := h16788c.2.1
                                    have p16788_2 := h16788c.2.2.1
                                    have p16788_3 := h16788c.2.2.2
                                    linarith only [hlam, p16788_0]
                          · linarith only [h15537, h16781, hlam]
                        · linarith only [h15534, h16780, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16922 | h16922
                        · linarith only [h0, h16922, hlam]
                        · rcases p16757_3 (m.d 0 2) (by simp) with h16924 | h16924
                          · rcases p16757_3 (m.d 0 3) (by simp) with h16925 | h16925
                            · linarith only [h15535, h16925, hlam]
                            · rcases p16757_3 (m.d 0 4) (by simp) with h16927 | h16927
                              · linarith only [h15536, h16927, hlam]
                              · rcases p16757_3 (m.d 0 5) (by simp) with h16929 | h16929
                                · linarith only [h15537, h16929, hlam]
                                · rcases h2bigk with h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c | h16931c
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, hlam, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15532, h16741, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15533, h16742, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15534, h16743, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15533, h16741, h16744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, h15533, h16741, h16744, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, h15533, h16742, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, h15534, h16743, hlam, p16757_1, p16931_2]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15535, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16741, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16750, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16752, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15536, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16742, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15534, h16742, h16748, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16757_1, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16754, hlam, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h15537, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h16743, hlam, p16931_0]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16757_1, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16757_1, p16931_1]
                                  · have p16931_0 := h16931c.1
                                    have p16931_1 := h16931c.2.1
                                    have p16931_2 := h16931c.2.2.1
                                    have p16931_3 := h16931c.2.2.2
                                    linarith only [hlam, p16931_0]
                          · linarith only [h0, h16924, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16959 | h16959
                        · linarith only [h0, h16959, hlam]
                        · linarith only [h15532, h16959, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16962 | h16962
                        · linarith only [h0, h16962, hlam]
                        · linarith only [h15533, h16962, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        rcases p16757_3 (m.d 0 1) (by simp) with h16965 | h16965
                        · linarith only [h0, h16965, hlam]
                        · linarith only [h15534, h16965, hlam]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15532, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15535, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15538, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h16013, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15533, hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15536, hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15532, h16176, h16741, h16756, hc23, hc34, hlam, hphi, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h16176, hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15534, hlam, p16757_0]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15537, hlam, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15532, h16176, h16741, h16756, hc23, hc34, hlam, hphi, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [h15536, h16176, h16750, h16756, hc23, hc34, hlam, hphi, p16757_1]
                      · have p16757_0 := h16757c.1
                        have p16757_1 := h16757c.2.1
                        have p16757_2 := h16757c.2.2.1
                        have p16757_3 := h16757c.2.2.2
                        linarith only [hlam, p16757_0]
                    · rcases h0bigk with h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c | h16983c
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h0, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h16986 | h16986
                        · rcases p16983_3 (m.d 0 2) (by simp) with h16987 | h16987
                          · rcases p16983_3 (m.d 0 3) (by simp) with h16988 | h16988
                            · linarith only [h15532, h16988, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h16990 | h16990
                              · linarith only [h15533, h16990, hlam]
                              · linarith only [h15538, h16990, hlam]
                          · linarith only [h15535, h16987, hlam]
                        · linarith only [h15532, h16986, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h16995 | h16995
                        · rcases p16983_3 (m.d 0 2) (by simp) with h16996 | h16996
                          · rcases p16983_3 (m.d 0 3) (by simp) with h16997 | h16997
                            · linarith only [h15532, h16997, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h16999 | h16999
                              · linarith only [h15533, h16999, hlam]
                              · rcases p16983_3 (m.d 0 5) (by simp) with h17001 | h17001
                                · linarith only [h15534, h17001, hlam]
                                · linarith only [h16176, h17001, hlam]
                          · linarith only [h15536, h16996, hlam]
                        · linarith only [h15533, h16995, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17006 | h17006
                        · rcases p16983_3 (m.d 0 2) (by simp) with h17007 | h17007
                          · rcases p16983_3 (m.d 0 3) (by simp) with h17008 | h17008
                            · linarith only [h15532, h17008, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h17010 | h17010
                              · linarith only [h15533, h17010, hlam]
                              · rcases p16983_3 (m.d 0 5) (by simp) with h17012 | h17012
                                · linarith only [h15534, h17012, hlam]
                                · rcases h2bigk with h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c | h17014c
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, hlam, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    rcases p17014_3 (m.d 0 2) (by simp) with h17017 | h17017
                                    · rcases p17014_3 (m.d 1 2) (by simp) with h17018 | h17018
                                      · rcases p17014_3 (m.d 2 3) (by simp) with h17019 | h17019
                                        · linarith only [h17019, hlam, p17014_0]
                                        · rcases p17014_3 (m.d 2 4) (by simp) with h17021 | h17021
                                          · linarith only [h15536, h17021, hlam]
                                          · linarith only [h16750, h17021, hlam]
                                      · linarith only [h16741, h17018, hlam]
                                    · linarith only [h17017, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    rcases p17014_3 (m.d 0 2) (by simp) with h17026 | h17026
                                    · rcases p17014_3 (m.d 1 2) (by simp) with h17027 | h17027
                                      · rcases p17014_3 (m.d 2 3) (by simp) with h17028 | h17028
                                        · linarith only [h15535, h17028, hlam]
                                        · rcases p17014_3 (m.d 2 4) (by simp) with h17030 | h17030
                                          · linarith only [h17030, hlam, p17014_0]
                                          · rcases p17014_3 (m.d 2 5) (by simp) with h17032 | h17032
                                            · linarith only [h15537, h17032, hlam]
                                            · linarith only [h16754, h17032, hlam]
                                      · linarith only [h16742, h17027, hlam]
                                    · linarith only [h17026, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    rcases p17014_3 (m.d 0 2) (by simp) with h17037 | h17037
                                    · rcases p17014_3 (m.d 1 2) (by simp) with h17038 | h17038
                                      · rcases p17014_3 (m.d 2 3) (by simp) with h17039 | h17039
                                        · linarith only [h15535, h17039, hlam]
                                        · rcases p17014_3 (m.d 2 4) (by simp) with h17041 | h17041
                                          · linarith only [h15536, h17041, hlam]
                                          · rcases p17014_3 (m.d 2 5) (by simp) with h17043 | h17043
                                            · linarith only [h17043, hlam, p17014_0]
                                            · rcases h3bigk with h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c | h17045c
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15538, h16741, h16756, hc23, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15538, h16756, hc23, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15538, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16013, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15532, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h0, h15532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16744, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16746, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15535, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16741, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16750, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16752, hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16756, hc03, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16756, hc13, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16756, hc23, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [hlam, p17045_0]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h16756, hlam, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                rcases p17045_3 (m.d 0 3) (by simp) with h17066 | h17066
                                                · linarith only [h17066, hlam, p17045_0]
                                                · rcases p17045_3 (m.d 1 3) (by simp) with h17068 | h17068
                                                  · linarith only [h16746, h17068, hlam]
                                                  · rcases p17045_3 (m.d 2 3) (by simp) with h17070 | h17070
                                                    · linarith only [h16752, h17070, hlam]
                                                    · rcases p17045_3 (m.d 3 4) (by simp) with h17072 | h17072
                                                      · linarith only [h16756, h17072, hlam]
                                                      · linarith only [h15538, h17072, hlam]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                rcases p17045_3 (m.d 0 3) (by simp) with h17075 | h17075
                                                · linarith only [h16013, h17075, hlam]
                                                · linarith only [h15532, h17075, hlam]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                rcases p17045_3 (m.d 0 3) (by simp) with h17078 | h17078
                                                · linarith only [h16013, h17078, hlam]
                                                · linarith only [h15535, h17078, hlam]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [h15538, h16756, hc03, hc45, hlam, hphi, ht34, p17045_1]
                                              · have p17045_0 := h17045c.1
                                                have p17045_1 := h17045c.2.1
                                                have p17045_2 := h17045c.2.2.1
                                                have p17045_3 := h17045c.2.2.2
                                                linarith only [hlam, p17045_0]
                                      · linarith only [h16743, h17038, hlam]
                                    · linarith only [h17037, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h16176, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p16983_1, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h15532, h15538, h16176, h16741, hlam, p16983_1, p17014_2]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h15536, h16176, hlam, p16983_1, p17014_2]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h15534, h16743, hlam, p16983_1, p17014_2]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h15535, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16741, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16750, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16752, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h15536, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16742, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h15533, h16176, h16742, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16983_1, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16754, hlam, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h15537, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h16743, hlam, p17014_0]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16983_1, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16983_1, p17014_1]
                                  · have p17014_0 := h17014c.1
                                    have p17014_1 := h17014c.2.1
                                    have p17014_2 := h17014c.2.2.1
                                    have p17014_3 := h17014c.2.2.2
                                    linarith only [hlam, p17014_0]
                          · linarith only [h15537, h17007, hlam]
                        · linarith only [h15534, h17006, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17107 | h17107
                        · linarith only [h0, h17107, hlam]
                        · rcases p16983_3 (m.d 0 2) (by simp) with h17109 | h17109
                          · rcases p16983_3 (m.d 0 3) (by simp) with h17110 | h17110
                            · linarith only [h15535, h17110, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h17112 | h17112
                              · linarith only [h15536, h17112, hlam]
                              · rcases p16983_3 (m.d 0 5) (by simp) with h17114 | h17114
                                · linarith only [h15537, h17114, hlam]
                                · rcases h2bigk with h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c | h17116c
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, hlam, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15532, h16741, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15533, h16742, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15534, h16743, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15533, h16741, h16744, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16983_1, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, h15533, h16741, h16744, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, h15533, h16742, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, h15534, h16743, hlam, p16983_1, p17116_2]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15535, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16741, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16750, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16752, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15536, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16742, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15534, h16742, h16748, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16983_1, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16754, hlam, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h15537, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h16743, hlam, p17116_0]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16983_1, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16983_1, p17116_1]
                                  · have p17116_0 := h17116c.1
                                    have p17116_1 := h17116c.2.1
                                    have p17116_2 := h17116c.2.2.1
                                    have p17116_3 := h17116c.2.2.2
                                    linarith only [hlam, p17116_0]
                          · linarith only [h0, h17109, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17144 | h17144
                        · linarith only [h0, h17144, hlam]
                        · linarith only [h15532, h17144, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17147 | h17147
                        · linarith only [h0, h17147, hlam]
                        · linarith only [h15533, h17147, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17150 | h17150
                        · linarith only [h0, h17150, hlam]
                        · linarith only [h15534, h17150, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15532, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15535, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15538, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h16013, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15533, hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15536, hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15532, h16176, h16741, hc23, hc45, hlam, hphi, ht34, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h16176, hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15534, hlam, p16983_0]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [h15537, hlam, p16983_1]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17165 | h17165
                        · rcases p16983_3 (m.d 0 2) (by simp) with h17166 | h17166
                          · rcases p16983_3 (m.d 0 3) (by simp) with h17167 | h17167
                            · linarith only [h16013, h17167, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h17169 | h17169
                              · linarith only [h16176, h17169, hlam]
                              · linarith only [h15538, h17169, hlam]
                          · linarith only [h15535, h17166, hlam]
                        · linarith only [h15532, h17165, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        rcases p16983_3 (m.d 0 1) (by simp) with h17174 | h17174
                        · rcases p16983_3 (m.d 0 2) (by simp) with h17175 | h17175
                          · rcases p16983_3 (m.d 0 3) (by simp) with h17176 | h17176
                            · linarith only [h16013, h17176, hlam]
                            · rcases p16983_3 (m.d 0 4) (by simp) with h17178 | h17178
                              · linarith only [h16176, h17178, hlam]
                              · rcases p16983_3 (m.d 0 5) (by simp) with h17180 | h17180
                                · rcases h2bigk with h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c | h17181c
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, hlam, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    rcases p17181_3 (m.d 0 2) (by simp) with h17184 | h17184
                                    · rcases p17181_3 (m.d 1 2) (by simp) with h17185 | h17185
                                      · rcases p17181_3 (m.d 2 3) (by simp) with h17186 | h17186
                                        · linarith only [h17186, hlam, p17181_0]
                                        · rcases p17181_3 (m.d 2 4) (by simp) with h17188 | h17188
                                          · linarith only [h15536, h17188, hlam]
                                          · linarith only [h16750, h17188, hlam]
                                      · linarith only [h16741, h17185, hlam]
                                    · linarith only [h17184, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    rcases p17181_3 (m.d 0 2) (by simp) with h17193 | h17193
                                    · rcases p17181_3 (m.d 1 2) (by simp) with h17194 | h17194
                                      · rcases p17181_3 (m.d 2 3) (by simp) with h17195 | h17195
                                        · linarith only [h15535, h17195, hlam]
                                        · rcases p17181_3 (m.d 2 4) (by simp) with h17197 | h17197
                                          · linarith only [h17197, hlam, p17181_0]
                                          · rcases p17181_3 (m.d 2 5) (by simp) with h17199 | h17199
                                            · linarith only [h15537, h17199, hlam]
                                            · linarith only [h16754, h17199, hlam]
                                      · linarith only [h16742, h17194, hlam]
                                    · linarith only [h17193, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    rcases p17181_3 (m.d 0 2) (by simp) with h17204 | h17204
                                    · rcases p17181_3 (m.d 1 2) (by simp) with h17205 | h17205
                                      · rcases p17181_3 (m.d 2 3) (by simp) with h17206 | h17206
                                        · linarith only [h15535, h17206, hlam]
                                        · rcases p17181_3 (m.d 2 4) (by simp) with h17208 | h17208
                                          · linarith only [h15536, h17208, hlam]
                                          · rcases p17181_3 (m.d 2 5) (by simp) with h17210 | h17210
                                            · linarith only [h17210, hlam, p17181_0]
                                            · rcases h3bigk with h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c | h17212c
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h15534, h15538, h16741, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16983_1, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h0, h15534, h15538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16983_1, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h15538, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16013, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h15532, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h0, h15532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16744, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16746, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h15535, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16741, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16750, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16752, hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16756, hc03, hc45, hlam, hphi, ht34, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16741, h16756, hc23, hc45, hlam, hphi, ht34, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16756, hc23, hc45, hlam, hphi, ht34, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [hlam, p17212_0]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h16756, hlam, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                rcases p17212_3 (m.d 0 3) (by simp) with h17233 | h17233
                                                · linarith only [h17233, hlam, p17212_0]
                                                · rcases p17212_3 (m.d 1 3) (by simp) with h17235 | h17235
                                                  · linarith only [h16746, h17235, hlam]
                                                  · rcases p17212_3 (m.d 2 3) (by simp) with h17237 | h17237
                                                    · linarith only [h16752, h17237, hlam]
                                                    · rcases p17212_3 (m.d 3 4) (by simp) with h17239 | h17239
                                                      · linarith only [h16756, h17239, hlam]
                                                      · linarith only [h15538, h17239, hlam]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                rcases p17212_3 (m.d 0 3) (by simp) with h17242 | h17242
                                                · linarith only [h16013, h17242, hlam]
                                                · linarith only [h15532, h17242, hlam]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                rcases p17212_3 (m.d 0 3) (by simp) with h17245 | h17245
                                                · linarith only [h16013, h17245, hlam]
                                                · linarith only [h15535, h17245, hlam]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [h15532, h15538, h16741, h16756, hc23, hc45, hlam, hphi, ht34, p17212_1]
                                              · have p17212_0 := h17212c.1
                                                have p17212_1 := h17212c.2.1
                                                have p17212_2 := h17212c.2.2.1
                                                have p17212_3 := h17212c.2.2.2
                                                linarith only [hlam, p17212_0]
                                      · linarith only [h16743, h17205, hlam]
                                    · linarith only [h17204, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, h15534, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p16983_1, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, h15532, h15534, h15538, h16741, hlam, p16983_1, p17181_2]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, h15534, h15536, hlam, p16983_1, p17181_2]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    rcases p17181_3 (m.d 0 2) (by simp) with h17256 | h17256
                                    · linarith only [h0, h17256, hlam]
                                    · linarith only [h15537, h17256, hlam]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h15535, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16741, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16750, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16752, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h15536, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16742, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h15533, h15534, h16742, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16983_1, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16754, hlam, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h15537, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h16743, hlam, p17181_0]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [h0, h15534, h16743, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p17181_1]
                                  · have p17181_0 := h17181c.1
                                    have p17181_1 := h17181c.2.1
                                    have p17181_2 := h17181c.2.2.1
                                    have p17181_3 := h17181c.2.2.2
                                    linarith only [hlam, p17181_0]
                                · linarith only [h16176, h17180, hlam]
                          · linarith only [h15536, h17175, hlam]
                        · linarith only [h15533, h17174, hlam]
                      · have p16983_0 := h16983c.1
                        have p16983_1 := h16983c.2.1
                        have p16983_2 := h16983c.2.2.1
                        have p16983_3 := h16983c.2.2.2
                        linarith only [hlam, p16983_0]
      · linarith only [h0, h15534, h15537, h16743, hc02, hc15, hlam, hphi, ht0b, ht5b]
    · linarith only [h0, h15536, h16742, hlam]
  · linarith only [h0, h15535, h16741, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h16013 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 4 5 (by decide) (by decide) with h16176 | h16176
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538 h16013 h16176
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538 h16013 h16176

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h15538 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 3 5 (by decide) (by decide) with h16013 | h16013
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538 h16013
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538 h16013

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 3 4 (by decide) (by decide) with h15538 | h15538
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537 h15538

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h15537 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h15534, h15537, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 5 (by decide) (by decide) with h15537 | h15537
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536 h15537

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h15536 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h15533, h15536, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 4 (by decide) (by decide) with h15536 | h15536
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535 h15536

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h15535 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  linarith only [h0, h15532, h15535, hlam]

set_option maxHeartbeats 5820000 in
set_option maxHeartbeats 5820000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h15533 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h15534 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  rcases m.htr 0 2 3 (by decide) (by decide) with h15535 | h15535
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s17_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg15532 h15533 h15534 h15535

end R2N4
