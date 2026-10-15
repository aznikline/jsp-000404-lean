import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S44

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15562000 in
set_option maxHeartbeats 15562000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s21 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  have h22350 := hg22350
  rcases m.htr 0 2 4 (by decide) (by decide) with h22351 | h22351
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s22 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350 h22351
  · rcases m.htr 0 2 5 (by decide) (by decide) with h29728 | h29728
    · rcases m.htr 0 3 4 (by decide) (by decide) with h29729 | h29729
      · linarith only [h22350, h22351, h29729, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h29731 | h29731
        · rcases m.htr 0 4 5 (by decide) (by decide) with h29732 | h29732
          · rcases m.htr 1 2 3 (by decide) (by decide) with h29733 | h29733
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29734 | h29734
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29735 | h29735
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29736 | h29736
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29737 | h29737
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29738 | h29738
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29739 | h29739
                        · linarith only [h20697, h22350, h22351, h29729, h29731, h29734, h29739, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29741 | h29741
                          · linarith only [h22350, h22351, h29733, h29736, h29739, h29741, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h22350, h22351, h29731, h29733, h29736, h29739, h29741, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h18443, h29732, h29738, hlam]
                    · linarith only [h22350, h22351, h29729, h29731, h29734, h29736, h29737, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29746 | h29746
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29747 | h29747
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29748 | h29748
                        · linarith only [h22350, h22351, h29734, h29736, h29748, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29750 | h29750
                          · linarith only [h22350, h22351, h29734, h29750, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h22350, h22351, h29731, h29734, h29750, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h22350, h22351, h29734, h29747, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h22350, h22351, h29731, h29734, h29746, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h22351, h29734, h29735, hc02, hc25, hlam, hphi]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29756 | h29756
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29757 | h29757
                  · linarith only [h29729, h29731, h29733, h29734, h29757, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29759 | h29759
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29760 | h29760
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29761 | h29761
                        · linarith only [h0, h22350, h29734, h29757, h29761, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29763 | h29763
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29764 | h29764
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29765 | h29765
                              · rcases h0bigk with h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c | h29766c
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h15532, hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h18443, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h20697, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, h29734, h29761, hc01, hc34, hlam, hphi, ht12, ht23, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, h29734, h29761, hc03, hc34, hlam, hphi, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h22351, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, h20697, h29734, h29761, hc01, hc34, hlam, hphi, ht12, ht23, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, h22350, h29734, h29761, hc01, hc34, hlam, hphi, ht12, ht23, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h22350, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h29729, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h0, h20697, h22350, h29734, h29761, hc01, hc34, hlam, hphi, ht12, ht23, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  rcases p29766_3 (m.d 0 1) (by simp) with h29782 | h29782
                                  · linarith only [h18443, h29782, hlam]
                                  · rcases p29766_3 (m.d 0 2) (by simp) with h29784 | h29784
                                    · linarith only [h22351, h29784, hlam]
                                    · linarith only [h0, h29784, hlam]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h18443, h22350, h29763, h29765, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  rcases p29766_3 (m.d 0 1) (by simp) with h29788 | h29788
                                  · linarith only [h18443, h29788, hlam]
                                  · rcases p29766_3 (m.d 0 2) (by simp) with h29790 | h29790
                                    · linarith only [h22351, h29790, hlam]
                                    · linarith only [h22350, h29790, hlam]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  rcases p29766_3 (m.d 0 1) (by simp) with h29794 | h29794
                                  · linarith only [h18443, h29794, hlam]
                                  · rcases p29766_3 (m.d 0 2) (by simp) with h29796 | h29796
                                    · linarith only [h22351, h29796, hlam]
                                    · linarith only [h29728, h29796, hlam]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h22351, h29728, h29761, hc01, hc34, hlam, hphi, ht12, ht23, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h29728, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h29731, hlam, p29766_0]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [h29732, hlam, p29766_1]
                                · have p29766_0 := h29766c.1
                                  have p29766_1 := h29766c.2.1
                                  have p29766_2 := h29766c.2.2.1
                                  have p29766_3 := h29766c.2.2.2
                                  linarith only [hlam, p29766_0]
                              · linarith only [h0, h29734, h29761, h29765, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h22350, h29731, h29732, h29734, h29764, hlam]
                          · linarith only [h0, h22350, h29731, h29734, h29761, h29763, hc23, hc34, hlam, hphi]
                      · linarith only [h18443, h22350, h22351, h29731, h29732, h29760, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h0, h15532, h22350, h29731, h29734, h29759, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h29728, h29756, hlam]
            · linarith only [h0, h22350, h29733, hlam]
          · linarith only [h22350, h22351, h29731, h29732, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h29812 | h29812
          · rcases m.htr 1 2 3 (by decide) (by decide) with h29813 | h29813
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29814 | h29814
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29815 | h29815
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29816 | h29816
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29817 | h29817
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29818 | h29818
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29819 | h29819
                        · linarith only [h22350, h22351, h29729, h29814, h29819, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29821 | h29821
                          · linarith only [h15532, h22350, h22351, h29731, h29813, h29816, h29819, h29821, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29823 | h29823
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29824 | h29824
                              · rcases h0bigk with h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c | h29825c
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [hlam, p29825_0]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h0, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h15532, hlam, p29825_0]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h18443, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h20697, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [hlam, p29825_0]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h15532, h22351, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, h29813, h29816, h29819, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h29731, h29817, hc01, hc15, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22350, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [hlam, p29825_0]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h29729, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h29731, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, h29728, h29813, h29816, h29819, h29821, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h15532, h22351, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [hlam, p29825_0]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h15532, h22351, h29731, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h22351, h29728, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h29728, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h15532, h22351, h29728, h29813, h29816, h29819, hc01, hc12, hlam, hphi, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [h29812, hlam, p29825_1]
                                · have p29825_0 := h29825c.1
                                  have p29825_1 := h29825c.2.1
                                  have p29825_2 := h29825c.2.2.1
                                  have p29825_3 := h29825c.2.2.2
                                  linarith only [hlam, p29825_0]
                              · linarith only [h22350, h22351, h29819, h29824, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h22351, h29728, h29812, h29823, hlam]
                      · linarith only [h18443, h22351, h29728, h29812, h29818, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h22350, h22351, h29729, h29816, h29817, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29855 | h29855
                    · linarith only [h15532, h29731, h29816, h29855, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29857 | h29857
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29858 | h29858
                        · linarith only [h22350, h22351, h29816, h29858, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29860 | h29860
                          · linarith only [h15532, h22350, h22351, h29814, h29855, h29860, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29862 | h29862
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29863 | h29863
                              · rcases h0bigk with h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c | h29864c
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [hlam, p29864_0]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h0, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, hlam, p29864_0]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h18443, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h20697, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [hlam, p29864_0]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, h22351, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, h29814, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, h29855, hc01, hc35, hlam, hphi, ht12, ht23, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22350, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [hlam, p29864_0]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h29729, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h29731, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, h29728, h29814, h29860, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, h22351, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [hlam, p29864_0]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, h22351, h29731, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h22351, h29728, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h29728, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h15532, h22351, h29728, h29814, hc01, hc12, hlam, hphi, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [h29812, hlam, p29864_1]
                                · have p29864_0 := h29864c.1
                                  have p29864_1 := h29864c.2.1
                                  have p29864_2 := h29864c.2.2.1
                                  have p29864_3 := h29864c.2.2.2
                                  linarith only [hlam, p29864_0]
                              · linarith only [h15532, h29816, h29863, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h22351, h29728, h29812, h29862, hlam]
                      · linarith only [h22351, h29728, h29812, h29814, h29857, hlam]
                · linarith only [h22351, h29728, h29814, h29815, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29894 | h29894
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29895 | h29895
                  · linarith only [h15532, h29729, h29813, h29814, h29895, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29897 | h29897
                    · linarith only [h15532, h29731, h29895, h29897, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29899 | h29899
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29900 | h29900
                        · linarith only [h18443, h22350, h22351, h29895, h29900, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29902 | h29902
                          · linarith only [h15532, h29897, h29902, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29904 | h29904
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29905 | h29905
                              · rcases h0bigk with h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c | h29906c
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [hlam, p29906_0]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h0, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h15532, hlam, p29906_0]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h18443, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h20697, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h0, h29814, hc01, hc24, hlam, hphi, ht12, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [hlam, p29906_0]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h0, h29814, h29900, hc03, hc34, hlam, hphi, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h22351, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h0, h20697, h29814, h29900, hc01, hc34, hlam, hphi, ht12, ht23, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h15532, h29814, h29894, h29897, h29900, hc01, hc34, hlam, hphi, ht12, ht23, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h22350, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [hlam, p29906_0]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h29729, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h29731, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  rcases p29906_3 (m.d 0 1) (by simp) with h29922 | h29922
                                  · linarith only [h18443, h29922, hlam]
                                  · rcases p29906_3 (m.d 0 2) (by simp) with h29924 | h29924
                                    · linarith only [h22351, h29924, hlam]
                                    · linarith only [h0, h29924, hlam]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h18443, h29728, h29814, h29900, h29902, hc23, hc34, hlam, hphi, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  rcases p29906_3 (m.d 0 1) (by simp) with h29928 | h29928
                                  · linarith only [h18443, h29928, hlam]
                                  · rcases p29906_3 (m.d 0 2) (by simp) with h29930 | h29930
                                    · linarith only [h22351, h29930, hlam]
                                    · linarith only [h22350, h29930, hlam]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [hlam, p29906_0]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  rcases p29906_3 (m.d 0 1) (by simp) with h29934 | h29934
                                  · linarith only [h18443, h29934, hlam]
                                  · rcases p29906_3 (m.d 0 2) (by simp) with h29936 | h29936
                                    · linarith only [h22351, h29936, hlam]
                                    · linarith only [h29728, h29936, hlam]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h20697, h29814, h29894, h29900, hc01, hc34, hlam, hphi, ht12, ht23, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h29728, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h15532, h20697, h29814, h29894, h29900, hc01, hc34, hlam, hphi, ht12, ht23, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [h29812, hlam, p29906_1]
                                · have p29906_0 := h29906c.1
                                  have p29906_1 := h29906c.2.1
                                  have p29906_2 := h29906c.2.2.1
                                  have p29906_3 := h29906c.2.2.2
                                  linarith only [hlam, p29906_0]
                              · linarith only [h0, h29814, h29900, h29905, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h15532, h29814, h29894, h29897, h29904, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h18443, h20697, h29812, h29814, h29894, h29899, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h29728, h29894, hlam]
            · linarith only [h0, h22350, h29813, hlam]
          · linarith only [h22351, h29728, h29812, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h29950 | h29950
      · linarith only [h22350, h22351, h29950, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h29952 | h29952
        · linarith only [h22350, h29728, h29952, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h29954 | h29954
          · rcases m.htr 1 2 3 (by decide) (by decide) with h29955 | h29955
            · rcases m.htr 1 2 4 (by decide) (by decide) with h29956 | h29956
              · rcases m.htr 1 2 5 (by decide) (by decide) with h29957 | h29957
                · rcases m.htr 1 3 4 (by decide) (by decide) with h29958 | h29958
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29959 | h29959
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29960 | h29960
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h29961 | h29961
                        · linarith only [h15532, h22350, h22351, h29950, h29956, h29961, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h29963 | h29963
                          · linarith only [h15532, h22350, h22351, h29952, h29955, h29958, h29961, h29963, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h29965 | h29965
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h29966 | h29966
                              · rcases h0bigk with h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c | h29967c
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h0, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h15532, hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h18443, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h20697, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h29728, h29955, h29958, h29961, h29965, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h15532, h29728, h29955, h29958, h29961, h29965, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22351, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h29728, hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22350, h29728, h29955, h29958, h29961, h29965, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22350, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h29950, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h29952, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22351, h29955, h29958, h29961, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22350, h22351, h29955, h29958, h29961, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h15532, h22351, h29955, h29958, h29961, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [hlam, p29967_0]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22350, h22351, h29728, h29955, h29958, h29961, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22351, h29954, h29955, h29958, h29961, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h22350, h29728, h29963, hc23, hc35, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h15532, h22351, h29954, h29955, h29958, h29961, hc01, hc12, hlam, hphi, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [h29954, hlam, p29967_1]
                                · have p29967_0 := h29967c.1
                                  have p29967_1 := h29967c.2.1
                                  have p29967_2 := h29967c.2.2.1
                                  have p29967_3 := h29967c.2.2.2
                                  linarith only [hlam, p29967_0]
                              · linarith only [h22351, h29954, h29961, h29966, hlam]
                            · linarith only [h22351, h29954, h29965, hlam]
                      · linarith only [h18443, h22351, h29954, h29960, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h22350, h22351, h29950, h29958, h29959, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h29997 | h29997
                    · linarith only [h15532, h29952, h29958, h29997, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h29999 | h29999
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h30000 | h30000
                        · linarith only [h22350, h22351, h29956, h30000, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h30002 | h30002
                          · linarith only [h22350, h29728, h29957, h29997, h30002, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30004 | h30004
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h30005 | h30005
                              · rcases h0bigk with h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c | h30006c
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h0, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h15532, hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h18443, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h20697, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29728, h29956, h30004, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29728, h29956, h30004, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22351, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29728, hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22350, h29728, h29956, h30004, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22350, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29950, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29952, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22351, h29956, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22350, h22351, h29956, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h15532, h22351, h29956, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [hlam, p30006_0]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h20697, h22351, h29956, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29728, h29956, h30004, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h22350, h29728, h29956, h30004, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h15532, h29728, h29956, h30004, hc01, hc12, hlam, hphi, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [h29954, hlam, p30006_1]
                                · have p30006_0 := h30006c.1
                                  have p30006_1 := h30006c.2.1
                                  have p30006_2 := h30006c.2.2.1
                                  have p30006_3 := h30006c.2.2.2
                                  linarith only [hlam, p30006_0]
                              · linarith only [h22351, h29954, h29956, h29958, h30005, hlam]
                            · linarith only [h22351, h29954, h30004, hlam]
                      · linarith only [h22351, h29954, h29956, h29999, hlam]
                · linarith only [h22350, h22351, h29956, h29957, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30036 | h30036
                · linarith only [h22350, h29728, h29956, h30036, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h30038 | h30038
                  · linarith only [h15532, h29950, h29955, h29956, h30038, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30040 | h30040
                    · linarith only [h15532, h29952, h30038, h30040, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30042 | h30042
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h30043 | h30043
                        · linarith only [h0, h22350, h29956, h30038, h30043, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h30045 | h30045
                          · linarith only [h22350, h29952, h30045, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30047 | h30047
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h30048 | h30048
                              · rcases h0bigk with h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c | h30049c
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h0, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h15532, hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h18443, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h20697, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h0, h30036, h30043, h30047, hc01, hc34, hlam, hphi, ht12, ht23, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h0, h30036, h30043, h30047, hc03, hc34, hlam, hphi, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h22351, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h29728, hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h0, h22350, h30036, h30043, h30047, hc01, hc34, hlam, hphi, ht12, ht23, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h22350, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h29950, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h29952, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  rcases p30049_3 (m.d 0 1) (by simp) with h30065 | h30065
                                  · linarith only [h18443, h30065, hlam]
                                  · rcases p30049_3 (m.d 0 2) (by simp) with h30067 | h30067
                                    · linarith only [h22351, h30067, hlam]
                                    · linarith only [h0, h30067, hlam]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h22350, h22351, h30043, hc23, hc34, hlam, hphi, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  rcases p30049_3 (m.d 0 1) (by simp) with h30071 | h30071
                                  · linarith only [h18443, h30071, hlam]
                                  · rcases p30049_3 (m.d 0 2) (by simp) with h30073 | h30073
                                    · linarith only [h22351, h30073, hlam]
                                    · linarith only [h22350, h30073, hlam]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [hlam, p30049_0]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h18443, h22350, h29728, h29956, h30043, hc23, hc34, hlam, hphi, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  rcases p30049_3 (m.d 0 1) (by simp) with h30078 | h30078
                                  · linarith only [h20697, h30078, hlam]
                                  · rcases p30049_3 (m.d 0 2) (by simp) with h30080 | h30080
                                    · linarith only [h29728, h30080, hlam]
                                    · linarith only [h0, h30080, hlam]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h20697, h22350, h30036, h30045, hc23, hc35, hlam, hphi, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  rcases p30049_3 (m.d 0 1) (by simp) with h30084 | h30084
                                  · linarith only [h20697, h30084, hlam]
                                  · rcases p30049_3 (m.d 0 2) (by simp) with h30086 | h30086
                                    · linarith only [h29728, h30086, hlam]
                                    · linarith only [h22350, h30086, hlam]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [h29954, hlam, p30049_1]
                                · have p30049_0 := h30049c.1
                                  have p30049_1 := h30049c.2.1
                                  have p30049_2 := h30049c.2.2.1
                                  have p30049_3 := h30049c.2.2.2
                                  linarith only [hlam, p30049_0]
                              · linarith only [h18443, h29954, h29956, h30043, h30048, hlam]
                            · linarith only [h18443, h29954, h29956, h30047, hlam]
                      · linarith only [h18443, h29954, h30042, hlam]
            · linarith only [h0, h22350, h29955, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h30095 | h30095
            · rcases m.htr 1 2 4 (by decide) (by decide) with h30096 | h30096
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30097 | h30097
                · rcases m.htr 1 3 4 (by decide) (by decide) with h30098 | h30098
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30099 | h30099
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30100 | h30100
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h30101 | h30101
                        · linarith only [h15532, h22350, h22351, h29950, h29954, h30098, h30100, h30101, hc01, hc13, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h30103 | h30103
                          · linarith only [h22350, h22351, h29954, h30095, h30098, h30100, h30103, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30105 | h30105
                            · linarith only [h22350, h22351, h29954, h30095, h30098, h30101, h30105, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h22350, h22351, h30105, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h22350, h22351, h30096, h30100, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h15532, h29950, h30098, h30099, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30110 | h30110
                    · linarith only [h15532, h29952, h30098, h30110, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30112 | h30112
                      · linarith only [h22350, h22351, h29954, h30098, h30112, hc23, hc34, hlam, hphi]
                      · linarith only [h22350, h22351, h30096, h30112, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h22350, h22351, h30096, h30097, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30116 | h30116
                · linarith only [h22350, h29728, h30096, h30116, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h30118 | h30118
                  · linarith only [h15532, h29950, h30095, h30096, h30118, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30120 | h30120
                    · linarith only [h15532, h29952, h30118, h30120, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h30122 | h30122
                      · linarith only [h22350, h22351, h29954, h30118, h30122, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h30124 | h30124
                        · linarith only [h0, h22350, h30096, h30118, h30122, h30124, hc13, hc45, hlam, hphi, ht34]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h30126 | h30126
                          · linarith only [h0, h20697, h22350, h30096, h30120, h30122, h30126, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h30128 | h30128
                            · linarith only [h15532, h30095, h30096, h30122, h30124, h30128, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h22350, h22351, h30128, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h22350, h22351, h30095, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h18443 := hg18443
  have h20697 := hg20697
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s21 m hb0 hb2 hb3 hb5 h0 h15532 h18443 h20697 h22350

end R2N4
