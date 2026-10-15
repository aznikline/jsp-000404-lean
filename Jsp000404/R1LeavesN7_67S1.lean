import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_67S0

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_14_25_L_0_L_0_H_I_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h746 | h746
  · rcases m.htr 0 1 5 (by decide) (by decide) with h747 | h747
    · rcases m.htr 0 2 3 (by decide) (by decide) with h748 | h748
      · rcases m.htr 0 2 5 (by decide) (by decide) with h749 | h749
        · rcases m.htr 0 3 4 (by decide) (by decide) with h750 | h750
          · rcases m.htr 0 3 5 (by decide) (by decide) with h751 | h751
            · rcases m.htr 0 4 5 (by decide) (by decide) with h752 | h752
              · rcases m.htr 1 2 3 (by decide) (by decide) with h753 | h753
                · rcases m.htr 1 2 4 (by decide) (by decide) with h754 | h754
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h755 | h755
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h756 | h756
                      · linarith only [h0, h746, h756, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h746, h750, h753, h756, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h755, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h754, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h746, h750, h753, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h762 | h762
                · rcases m.htr 1 2 4 (by decide) (by decide) with h763 | h763
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h764 | h764
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h765 | h765
                      · linarith only [h0, h746, h765, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h0, h746, h750, h765, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h764, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h746, h762, h763, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h762, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h771 | h771
              · linarith only [h750, h751, h771, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                      · linarith only [h0, h746, h776, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h750, h751, h773, h776, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h775, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h747, h750, h751, h774, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h747, h750, h751, h773, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h782 | h782
            · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                      · linarith only [h0, h746, h750, h787, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h789 | h789
                        · linarith only [h0, h746, h789, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h750, h782, h789, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h786, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h785, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h746, h784, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h750, h782, h783, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h796 | h796
              · rcases m.htr 1 2 3 (by decide) (by decide) with h797 | h797
                · rcases m.htr 1 2 4 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h799 | h799
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h800 | h800
                      · linarith only [h0, h746, h800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h802 | h802
                        · linarith only [h746, h782, h802, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h804 | h804
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h805 | h805
                            · linarith only [h0, h747, h797, h798, h800, h802, h805, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h807 | h807
                              · linarith only [h746, h782, h797, h807, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h809 | h809
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h810 | h810
                                  · rcases h5bigk with h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c | h811c
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h796, h797, h802, hc23, hlam, hphi, ht34, p811_1, u4elo0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p811_1, u2elo1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h782, hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p811_1, u2elo1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h747, hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p811_1, u2elo1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h802, hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p811_1, u2elo1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h749, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h799, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h807, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p811_1, u2elo4]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, h749, h797, h802, h810, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p811_1, u2elo1, u4elo3]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h797, h802, h810, hc23, hlam, hphi, ht34, p811_1, u4elo3]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, h797, h802, h810, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p811_1, u2elo1, u4elo3]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hlam, p811_0]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h0, h747, h797, h802, h810, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p811_1, u2elo1, u4elo3]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h796, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h804, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h809, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [h810, hlam, p811_1]
                                    · have p811_0 := h811c.1
                                      have p811_1 := h811c.2.1
                                      have p811_2 := h811c.2.2.1
                                      have p811_3 := h811c.2.2.2
                                      linarith only [hlam, p811_0]
                                  · linarith only [h750, h798, h809, h810, hc04, hlam, hphi, u4elo1]
                                · linarith only [h0, h747, h804, h809, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h796, h804, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h799, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h746, h797, h798, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h797, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h843 | h843
                · rcases m.htr 1 2 4 (by decide) (by decide) with h844 | h844
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h845 | h845
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h846 | h846
                      · linarith only [h0, h746, h846, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h848 | h848
                        · linarith only [h0, h746, h848, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h850 | h850
                          · linarith only [h750, h796, h850, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h852 | h852
                            · linarith only [h0, h746, h843, h852, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h854 | h854
                              · linarith only [h746, h782, h843, h854, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h856 | h856
                                · linarith only [h0, h747, h844, h850, h856, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h858 | h858
                                  · linarith only [h746, h750, h796, h843, h858, hc23, hlam, hphi, ht34, u4elo3]
                                  · linarith only [h746, h750, h843, h858, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h845, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h746, h843, h844, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h746, h843, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h747, h749, hlam]
      · linarith only [h0, h746, h748, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h866 | h866
      · rcases m.htr 0 2 5 (by decide) (by decide) with h867 | h867
        · rcases m.htr 0 3 4 (by decide) (by decide) with h868 | h868
          · rcases m.htr 0 3 5 (by decide) (by decide) with h869 | h869
            · linarith only [h746, h747, h869, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h871 | h871
              · linarith only [h746, h747, h868, h871, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h873 | h873
                · rcases m.htr 1 2 4 (by decide) (by decide) with h874 | h874
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h875 | h875
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
                      · linarith only [h746, h747, h875, h876, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h868, h869, h876, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h746, h873, h875, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h746, h873, h874, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h873, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h882 | h882
            · linarith only [h746, h747, h868, h882, hc13, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
              · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h888 | h888
                      · linarith only [h746, h747, h868, h887, h888, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h890 | h890
                        · linarith only [h746, h747, h882, h890, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                          · linarith only [h746, h747, h885, h892, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h884, h892, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h746, h885, h887, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h746, h885, h886, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h746, h885, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h898 | h898
                · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
                      · linarith only [h746, h747, h900, h901, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h903 | h903
                        · linarith only [h746, h747, h900, h903, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h905 | h905
                          · linarith only [h868, h884, h905, hc03, hlam, hphi, ht34, u4elo1]
                          · linarith only [h746, h747, h898, h905, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h867, h900, hlam]
                  · linarith only [h0, h746, h898, h899, hc23, hlam, hphi, ht34, u4elo2]
                · linarith only [h0, h898, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h911 | h911
          · rcases m.htr 0 3 5 (by decide) (by decide) with h912 | h912
            · linarith only [h746, h747, h912, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h914 | h914
              · linarith only [h0, h746, h867, h911, h914, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h916 | h916
                · rcases m.htr 1 2 4 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h918 | h918
                    · linarith only [h0, h867, h918, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h746, h916, h918, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h746, h916, h917, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h916, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h923 | h923
            · linarith only [h0, h746, h867, h911, h923, hc13, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
              · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
                · rcases m.htr 1 2 4 (by decide) (by decide) with h927 | h927
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h928 | h928
                    · linarith only [h0, h746, h867, h926, h928, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h746, h926, h928, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h746, h926, h927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h746, h926, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h933 | h933
                · rcases m.htr 1 2 4 (by decide) (by decide) with h934 | h934
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h935 | h935
                    · linarith only [h867, h935, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h746, h933, h935, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h746, h933, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h746, h933, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h746, h866, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h941 | h941
    · rcases m.htr 0 2 3 (by decide) (by decide) with h942 | h942
      · rcases m.htr 0 2 5 (by decide) (by decide) with h943 | h943
        · rcases m.htr 0 3 4 (by decide) (by decide) with h944 | h944
          · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
            · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
              · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h949 | h949
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h950 | h950
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h951 | h951
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h952 | h952
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h953 | h953
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h954 | h954
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                                  · linarith only [h942, h953, h956, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h946, h956, hc34, hlam, hphi, u4elo0]
                                · linarith only [h952, h955, hc24, hlam, hphi, u4elo1]
                              · linarith only [h746, h941, h947, h951, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h961 | h961
                              · linarith only [h746, h944, h947, h953, h961, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h746, h941, h947, h951, h961, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · linarith only [h946, h952, hc14, hlam, hphi, u4elo0]
                        · linarith only [h746, h945, h951, hlam]
                      · linarith only [h746, h944, h950, hlam]
                    · linarith only [h746, h947, h949, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h746, h947, h948, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h941, h947, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h970 | h970
                · rcases m.htr 1 2 4 (by decide) (by decide) with h971 | h971
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h972 | h972
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h973 | h973
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h974 | h974
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h975 | h975
                          · linarith only [h944, h946, h975, hc34, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h977 | h977
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h978 | h978
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h979 | h979
                                · linarith only [h0, h941, h971, h975, h979, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h981 | h981
                                  · linarith only [h746, h941, h946, h970, h971, h975, h977, h981, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                                  · rcases h5bigk with h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, h975, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p983_1, u2elo1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h946, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h941, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, h978, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h975, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h943, hlam, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h972, hlam, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo4]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h979, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h945, hlam, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h974, hlam, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h978, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h981, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p983_1, u4elo4]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h972, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p983_1, u4elo4]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, h971, h975, h977, h978, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1, u4elo4]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h746, h941, h970, h971, h975, h977, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u2elo1, u4elo4]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                              · linarith only [h746, h941, h970, h974, h978, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · linarith only [h746, h941, h970, h973, h975, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h746, h942, h945, h974, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h746, h973, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h746, h941, h970, h972, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · linarith only [h746, h941, h970, h971, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h941, h970, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h746, h941, h945, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1017 | h1017
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1018 | h1018
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1019 | h1019
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1020 | h1020
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1021 | h1021
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                      · linarith only [h1019, h1022, h746, h944, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1021, h1022, h746, h941, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h1021, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1019, h1020, h746, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h1019, h942, hc12, hlam, hphi, u2elo0]
              · linarith only [h1018, h746, h941, h944, hlam]
            · linarith only [h1017, h746, h941, hlam]
        · linarith only [h0, h941, h943, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1031 | h1031
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1032 | h1032
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1033 | h1033
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1034 | h1034
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1035 | h1035
                · linarith only [h1031, h1035, h942, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1035, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1038 | h1038
                · linarith only [h0, h1038, h941, h942, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1038, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
            · linarith only [h0, h1033, h941, h942, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1042 | h1042
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1043 | h1043
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1044 | h1044
                · linarith only [h0, h1044, h941, h942, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1044, h941, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h0, h1032, h1043, h941, h942, hlam]
            · linarith only [h0, h1042, h941, h942, hlam]
        · linarith only [h0, h1031, h941, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1050 | h1050
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1051 | h1051
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1052 | h1052
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1053 | h1053
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1054 | h1054
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1055 | h1055
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1056 | h1056
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1057 | h1057
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1058 | h1058
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1060 | h1060
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1061 | h1061
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1062 | h1062
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                                  · linarith only [h1050, h1061, h1064, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h1054, h1064, hc34, hlam, hphi, u4elo0]
                                · linarith only [h1054, h1063, hc24, hlam, hphi, u4elo0]
                              · linarith only [h1053, h1055, h1061, h1062, h746, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1069 | h1069
                              · linarith only [h1052, h1055, h1061, h1069, h746, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1071 | h1071
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1072 | h1072
                                  · rcases h5bigk with h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hlam, p1073_0]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h941, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1060, h941, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1073_1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1060, h1069, h941, hc23, hlam, hphi, ht34, p1073_1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1060, h1069, h1072, h746, h941, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p1073_1, u2elo1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1060, h1069, h1072, h746, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p1073_1, u2elo1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hlam, p1073_0]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1060, h1069, h1072, h746, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p1073_1, u2elo1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1060, h1069, hc23, hlam, hphi, ht34, p1073_1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1060, h1069, h1072, h746, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p1073_1, u2elo1, u4elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1051, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1057, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hlam, p1073_0]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1069, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1, u2elo4]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1053, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1059, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1072, h746, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1, u2elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hlam, p1073_0]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1052, h1055, h1072, h746, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1, u2elo1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1054, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1060, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1071, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [h1072, hlam, p1073_1]
                                    · have p1073_0 := h1073c.1
                                      have p1073_1 := h1073c.2.1
                                      have p1073_2 := h1073c.2.2.1
                                      have p1073_3 := h1073c.2.2.2
                                      linarith only [hlam, p1073_0]
                                  · linarith only [h1054, h1061, h1072, hc24, hlam, hphi, u4elo0]
                                · linarith only [h1054, h1061, h1071, hc23, hlam, hphi, ht34, u4elo0]
                          · linarith only [h1054, h1060, hc14, hlam, hphi, u4elo0]
                        · linarith only [h1053, h1059, h746, hlam]
                      · linarith only [h1058, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1057, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1050, h1052, h1056, hc34, hlam, hphi, u4elo2]
                · linarith only [h0, h1055, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1110 | h1110
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1111 | h1111
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1112 | h1112
                          · linarith only [h1054, h1112, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1114 | h1114
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1115 | h1115
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                                · linarith only [h1108, h1112, h1116, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1118 | h1118
                                  · linarith only [h1050, h1112, h1114, h1118, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h5bigk with h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h941, hlam, p1120_1]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h0, h1050, h1112, h1115, h1118, h941, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p1120_1, u2elo1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1112, h1118, h941, hc34, hlam, hphi, p1120_1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1054, hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h0, h1050, h1112, h1115, h1118, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p1120_1, u2elo1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h0, h1050, h1112, h1115, h1118, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p1120_1, u2elo1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1112, h1118, hc34, hlam, hphi, p1120_1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1112, hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1051, hlam, p1120_1]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1109, hlam, p1120_1]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1118, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1120_1, u2elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1116, hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1053, hlam, p1120_1]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1111, hlam, p1120_1]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1115, hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1118, hlam, p1120_0]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h941, hc01, hlam, hphi, ht12, ht23, ht34, p1120_1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1120_1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h0, h1050, h1115, h1118, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p1120_1, u2elo1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [h1118, hc34, hlam, hphi, p1120_1, u4elo4]
                                    · have p1120_0 := h1120c.1
                                      have p1120_1 := h1120c.2.1
                                      have p1120_2 := h1120c.2.2.1
                                      have p1120_3 := h1120c.2.2.2
                                      linarith only [hlam, p1120_0]
                              · linarith only [h0, h1050, h1053, h1114, h1115, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h1052, h1054, h1114, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1053, h1111, h746, hlam]
                      · linarith only [h1110, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1109, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1108, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1107, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1153 | h1153
              · linarith only [h1052, h1053, h1153, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1155 | h1155
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1156 | h1156
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1157 | h1157
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1158 | h1158
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1159 | h1159
                        · linarith only [h1053, h1155, h1159, h746, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1161 | h1161
                          · linarith only [h1153, h1161, hc04, hlam, hphi, u4elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1163 | h1163
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1164 | h1164
                              · linarith only [h1159, h1164, h746, hc01, hlam, hphi, ht12, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1166 | h1166
                                · linarith only [h1156, h1161, h1166, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1168 | h1168
                                  · linarith only [h0, h1051, h1053, h1161, h1163, h1164, h1168, h941, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                  · linarith only [h1159, h1168, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                            · linarith only [h1052, h1159, h1163, h746, hc23, hc35, hlam, hphi]
                      · linarith only [h1052, h1158, h746, hlam]
                    · linarith only [h0, h1051, h1157, hlam]
                  · linarith only [h0, h1156, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1155, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1176 | h1176
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1177 | h1177
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1178 | h1178
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1179 | h1179
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1180 | h1180
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1181 | h1181
                      · linarith only [h1052, h1176, h1178, h1181, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1181, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1180, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1179, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1178, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1052, h1176, h1177, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1188 | h1188
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1190 | h1190
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1192 | h1192
                      · linarith only [h1052, h1189, h1192, h746, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1192, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1191, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1189, h1190, h746, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1050, h1189, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1198 | h1198
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1200 | h1200
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1201 | h1201
                      · linarith only [h1052, h1198, h1201, h746, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1201, h746, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1051, h1200, hlam]
                  · linarith only [h0, h1199, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h1198, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1207 | h1207
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1208 | h1208
            · linarith only [h1050, h1051, h1208, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1210 | h1210
              · linarith only [h1050, h1051, h1207, h1210, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1212 | h1212
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1213 | h1213
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1214 | h1214
                    · linarith only [h1051, h1214, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1214, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1212, h1213, h746, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1050, h1212, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1219 | h1219
            · linarith only [h1050, h1051, h1207, h1219, hc23, hlam, hphi, ht34, u4elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1221 | h1221
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1223 | h1223
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1224 | h1224
                    · linarith only [h1050, h1051, h1224, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1224, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1222, h1223, h746, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1050, h1222, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
                    · linarith only [h1051, h1231, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1231, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1229, h1230, h746, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h1050, h1229, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1236 | h1236
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1237 | h1237
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1238 | h1238
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1239 | h1239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1240 | h1240
                · linarith only [h1050, h1240, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1240, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1243 | h1243
                · linarith only [h1050, h1236, h1243, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1243, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1050, h1236, h1238, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1249 | h1249
                · linarith only [h1050, h1236, h1249, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1249, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1050, h1236, h1237, h1248, hlam]
            · linarith only [h1050, h1236, h1247, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1254 | h1254
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1255 | h1255
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1256 | h1256
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1257 | h1257
                · linarith only [h0, h1050, h1257, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1257, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1260 | h1260
                · linarith only [h0, h1050, h1260, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1260, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1263 | h1263
              · linarith only [h1254, h1255, h1263, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1265 | h1265
                · linarith only [h0, h1050, h1265, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1265, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1268 | h1268
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1269 | h1269
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1270 | h1270
                · linarith only [h0, h1050, h1270, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1270, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1254, h1268, h1269, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                · linarith only [h0, h1050, h1275, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1275, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1278 | h1278
                · linarith only [h0, h1050, h1278, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1278, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_12_14_25_L_0_L_0_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_14_25_L_0_L_0_H_I_x0 m hb2 hb4 hb5 h0
  · exact r1l7_12_14_25_L_0_L_0_H_I_x1 m hb2 hb4 hb5 h0

theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h12, h13, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h0, h11, h13, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h11, h12, h19, h8, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h11, h12, h2, h21, h6, h9, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h12, h18, h2, h21, h23, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases h0bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h12, h23, h5, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi2]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h11, h12, h23, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p25_1, u5ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h11, h12, h23, h5, h7, h9, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, h11, h12, h23, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p25_1, u5ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h1, hlam, p25_1]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h2, hlam, p25_1]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h11, h12, h23, h7, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p25_1, u5ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h3, hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h5, hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, h11, h12, h2, h23, h5, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi3]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p25_1, u2ehi0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h4, hlam, p25_1]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h6, hlam, p25_0]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [h7, hlam, p25_1]
                                  · have p25_0 := h25c.1
                                    have p25_1 := h25c.2.1
                                    have p25_2 := h25c.2.2.1
                                    have p25_3 := h25c.2.2.2
                                    linarith only [hlam, p25_0]
                          · linarith only [h11, h12, h18, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                        · linarith only [h0, h11, h2, h5, h52, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                          · linarith only [h0, h11, h54, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                            · linarith only [h52, h56, h8, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                              · linarith only [h0, h58, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                                · linarith only [h58, h60, hc34, hlam, hphi, ht23, u2ehi3]
                                · linarith only [h0, h11, h2, h5, h60, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
                  · linarith only [h65, h8, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h2, h67, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h69 | h69
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h70 | h70
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h72 | h72
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h73 | h73
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h74 | h74
                                · linarith only [h1, h69, h74, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0bigk with h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c | h76c
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h5, h7, hc01, hlam, hphi, ht0b, ht5b, p76_1, u5ehi0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h3, h67, h73, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h4, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h2, h67, h71, h73, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, h3, h67, h73, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, h4, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h1, hlam, p76_1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h2, hlam, p76_1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h3, h67, h73, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, h2, h4, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h3, hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h5, hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, h2, h4, h5, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p76_1, u2ehi0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h4, hlam, p76_1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h6, hlam, p76_0]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [h7, hlam, p76_1]
                                  · have p76_0 := h76c.1
                                    have p76_1 := h76c.2.1
                                    have p76_2 := h76c.2.2.1
                                    have p76_3 := h76c.2.2.2
                                    linarith only [hlam, p76_0]
                              · linarith only [h0, h2, h5, h65, h7, h73, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h65, h71, h72, hc35, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h0, h2, h5, h70, h71, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h106 | h106
                            · linarith only [h0, h106, h2, h69, h70, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                            · linarith only [h0, h106, h2, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h105, h8, hc34, hlam, hphi, ht23, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                        · linarith only [h0, h110, h2, h5, h69, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                          · linarith only [h0, h112, h2, h69, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · linarith only [h0, h112, h2, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h117 | h117
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                            · linarith only [h0, h115, h121, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h1, h119, h120, h121, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h120, h5, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h126 | h126
                            · linarith only [h0, h115, h119, h126, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h128 | h128
                              · linarith only [h128, h3, h7, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                                · linarith only [h116, h118, h119, h130, h6, h7, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h0bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h116, h118, h119, h2, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h116, h118, h119, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h116, h118, h119, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h116, h118, h119, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, h116, h118, h119, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h1, hlam, p132_1]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h2, hlam, p132_1]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, h116, h118, h119, h2, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h3, hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h5, hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h7, hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h0, h116, h118, h119, h2, h6, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1, u2ehi3]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h4, hlam, p132_1]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h6, hlam, p132_0]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [h7, hc04, hc45, hlam, hphi, p132_1]
                                  · have p132_0 := h132c.1
                                    have p132_1 := h132c.2.1
                                    have p132_2 := h132c.2.2.1
                                    have p132_3 := h132c.2.2.2
                                    linarith only [hlam, p132_0]
                          · linarith only [h125, h5, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h115, h118, h5, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h115, h117, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h115, h116, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h162 | h162
                  · linarith only [h115, h162, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h162, h3, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
              · linarith only [h165, h5, h6, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h169 | h169
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h170 | h170
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h171 | h171
                        · linarith only [h1, h171, h6, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h174 | h174
                            · linarith only [h1, h168, h170, h174, h6, hc23, hlam, hphi, u2ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                              · linarith only [h165, h176, h3, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h178 | h178
                                · linarith only [h165, h178, h3, hc34, hlam, hphi, ht23, u2ehi3]
                                · rcases h0bigk with h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c | h180c
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, h168, h170, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht0b, ht5b, p180_1, u5ehi0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, h168, h170, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p180_1, u5ehi0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h1, hlam, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h2, hlam, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h6, hlam, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h3, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h5, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h165, hlam, p180_0]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h4, hlam, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h0, h1, h168, h170, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p180_1, u2ehi3]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [h178, h6, hc04, hc45, hlam, hphi, p180_1]
                                  · have p180_0 := h180c.1
                                    have p180_1 := h180c.2.1
                                    have p180_2 := h180c.2.2.1
                                    have p180_3 := h180c.2.2.2
                                    linarith only [hlam, p180_0]
                          · linarith only [h173, h5, h6, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h170, h5, h6, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h167, h169, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h167, h168, hc24, hlam, hphi, u2ehi2]
                · linarith only [h167, h2, h6, hc35, hlam, hphi, ht23, u2ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
            · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h215 | h215
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h216 | h216
                      · linarith only [h211, h216, h5, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h218 | h218
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                          · linarith only [h0, h1, h213, h218, h219, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                            · linarith only [h0, h214, h219, h221, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h1, h218, h221, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h211, h218, h5, hc13, hc34, hlam, hphi]
                    · linarith only [h214, h215, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h213, h214, hc24, hlam, hphi, u2ehi2]
                · linarith only [h2, h213, h5, hc34, hlam, hphi, ht23, u2ehi1]
              · linarith only [h211, h212, h5, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h229 | h229
              · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                      · linarith only [h1, h233, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h235 | h235
                        · linarith only [h1, h211, h235, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h237 | h237
                          · linarith only [h1, h230, h237, h5, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h239 | h239
                            · linarith only [h1, h211, h230, h239, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                              · linarith only [h0, h231, h241, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h229, h237, h241, h5, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h231, h232, hc25, hlam, hphi, u2ehi3]
                  · linarith only [h230, h231, hc24, hlam, hphi, u2ehi2]
                · linarith only [h2, h211, h230, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h247 | h247
                · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                      · linarith only [h1, h250, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                        · linarith only [h1, h211, h252, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h254 | h254
                          · linarith only [h2, h254, h5, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h256 | h256
                            · linarith only [h1, h211, h247, h256, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                              · linarith only [h0, h229, h248, h258, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h1, h229, h247, h260, h5, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h1, h247, h260, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h247, h249, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h247, h248, hc24, hlam, hphi, u2ehi2]
                · linarith only [h2, h247, h5, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h4, hc25, hlam, hphi, u2ehi2]
      · linarith only [h2, h3, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h268 | h268
      · linarith only [h2, h268, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h270 | h270
        · linarith only [h2, h270, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h272 | h272
          · rcases m.htr 0 3 5 (by decide) (by decide) with h273 | h273
            · rcases m.htr 0 4 5 (by decide) (by decide) with h274 | h274
              · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
                · linarith only [h0, h2, h275, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h268, h277, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h279 | h279
                    · linarith only [h0, h270, h279, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h286 | h286
                                · linarith only [h1, h281, h286, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h272, h274, hc01, hlam, hphi, ht0b, ht5b, p288_1, u5ehi4]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h274, h286, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, h270, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h2, hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h268, hlam, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h270, hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h1, hlam, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h2, h274, h286, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, h2, h270, hc23, hlam, hphi, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, h268, h283, hc23, hlam, hphi, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h272, hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, h268, h270, h283, hc23, hlam, hphi, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1, u2ehi1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h273, hlam, p288_0]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [h274, hlam, p288_1]
                                  · have p288_0 := h288c.1
                                    have p288_1 := h288c.2.1
                                    have p288_2 := h288c.2.2.1
                                    have p288_3 := h288c.2.2.2
                                    linarith only [hlam, p288_0]
                              · linarith only [h0, h268, h285, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h1, h282, h284, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h2, h283, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h2, h273, h275, h282, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h2, h272, h275, h281, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h319 | h319
                · linarith only [h0, h2, h273, h319, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
                  · linarith only [h0, h268, h274, h321, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h323 | h323
                    · linarith only [h0, h268, h274, h323, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h326 | h326
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h327 | h327
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h329 | h329
                              · linarith only [h268, h274, h329, hc24, hlam, hphi, u2ehi0]
                              · linarith only [h0, h268, h329, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h1, h326, h328, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h2, h327, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h2, h273, h319, h326, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h2, h272, h319, h325, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h336 | h336
              · linarith only [h272, h273, h336, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
                · linarith only [h0, h2, h338, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
                  · linarith only [h0, h2, h340, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h342 | h342
                    · linarith only [h0, h268, h336, h342, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                        · linarith only [h1, h273, h345, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h348 | h348
                            · linarith only [h268, h272, h273, h348, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h0, h2, h348, hc35, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h0, h2, h347, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h272, h273, h344, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h353 | h353
            · rcases m.htr 0 4 5 (by decide) (by decide) with h354 | h354
              · rcases m.htr 1 2 3 (by decide) (by decide) with h355 | h355
                · linarith only [h0, h2, h355, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h357 | h357
                  · linarith only [h0, h268, h357, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h359 | h359
                    · linarith only [h0, h270, h359, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                      · linarith only [h272, h353, h361, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h363 | h363
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h364 | h364
                          · linarith only [h1, h272, h363, h364, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h2, h364, hc34, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h272, h353, h363, hc13, hc34, hlam, hphi]
              · linarith only [h272, h353, h354, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
              · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                · linarith only [h0, h2, h370, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                  · linarith only [h0, h268, h372, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                    · linarith only [h0, h270, h374, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                      · linarith only [h0, h1, h2, h272, h376, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                        · linarith only [h1, h353, h378, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                          · linarith only [h0, h2, h272, h380, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h2, h380, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                · linarith only [h0, h2, h383, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                  · linarith only [h0, h268, h385, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
                    · linarith only [h0, h270, h387, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
                      · linarith only [h1, h272, h389, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h391 | h391
                        · linarith only [h1, h353, h391, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h393 | h393
                          · linarith only [h0, h2, h272, h393, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h0, h2, h393, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h396 | h396
    · linarith only [h0, h1, h396, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
      · linarith only [h396, h398, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
        · linarith only [h396, h400, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
          · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
            · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                · linarith only [h0, h1, h396, h405, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h405, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h408 | h408
                · linarith only [h0, h1, h408, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h408, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h403, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h402, hc34, hlam, hphi, ht23, u2ehi1]

theorem r1l7_20_12_13_15_H_I_L_R_L_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h413 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2ehi := hb2.1
  have h5ehi := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h414 | h414
  · rcases m.htr 0 2 4 (by decide) (by decide) with h415 | h415
    · rcases m.htr 0 2 5 (by decide) (by decide) with h416 | h416
      · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
        · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
          · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
            · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
              · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
                · rcases m.htr 1 2 5 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h424 | h424
                      · linarith only [h0, h413, h424, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h413, h418, h421, h423, h424, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h0, h413, h417, h420, h423, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h413, h416, h417, h422, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h413, h420, h421, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h415, h420, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
              · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                · rcases m.htr 1 2 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h434 | h434
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h435 | h435
                      · linarith only [h0, h413, h435, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h413, h418, h431, h435, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h413, h417, h431, h434, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h413, h418, h433, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · linarith only [h0, h413, h431, h432, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h413, h418, h431, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
            · linarith only [h417, h418, h442, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
              · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                      · linarith only [h413, h418, h448, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h450 | h450
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h451 | h451
                          · linarith only [h414, h418, h451, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                            · linarith only [h415, h442, h453, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                              · linarith only [h415, h442, h455, hc34, hlam, hphi, ht23, u2ehi3]
                              · rcases h0bigk with h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h413, h445, h447, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, h415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, h413, h418, h445, h447, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, h413, h445, h447, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, h415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h0, h413, h418, h445, h447, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h413, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h414, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h415, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h418, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h413, h445, h447, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h415, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h417, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h442, hlam, p457_0]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h413, h418, h445, h447, h455, hc45, hlam, hphi, ht23, ht34, p457_1, u2ehi3]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h416, hlam, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h418, h455, hc03, hc45, hlam, hphi, ht34, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [h418, h455, hc04, hc45, hlam, hphi, p457_1]
                                · have p457_0 := h457c.1
                                  have p457_1 := h457c.2.1
                                  have p457_2 := h457c.2.2.1
                                  have p457_3 := h457c.2.2.2
                                  linarith only [hlam, p457_0]
                        · linarith only [h0, h413, h417, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h417, h418, h447, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h413, h444, h446, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h413, h415, h444, h445, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h0, h415, h444, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
          · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
            · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
              · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                · rcases m.htr 1 2 5 (by decide) (by decide) with h492 | h492
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                    · linarith only [h0, h413, h417, h488, h493, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h495 | h495
                      · linarith only [h0, h413, h495, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · linarith only [h417, h488, h490, h495, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h413, h416, h490, h492, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h413, h490, h491, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h413, h488, h490, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h417, h488, h489, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h502 | h502
            · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
              · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                    · linarith only [h413, h417, h502, h506, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h508 | h508
                      · linarith only [h0, h413, h488, h508, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h510 | h510
                        · linarith only [h413, h417, h503, h510, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h512 | h512
                          · linarith only [h413, h488, h503, h512, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h514 | h514
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                              · rcases h0bigk with h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c | h516c
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [hlam, p516_0]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h413, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h415, h514, hc12, hlam, hphi, ht01, ht0b, ht5b, p516_1, u5ehi4]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h413, h488, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, hc01, hc12, hlam, hphi, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [hlam, p516_0]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h413, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h415, h514, hc12, hlam, hphi, ht01, ht0b, ht5b, p516_1, u5ehi4]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h0, h413, h488, h503, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h414, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [hlam, p516_0]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h417, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h488, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, h503, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h415, hlam, p516_0]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, h503, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [hlam, p516_0]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, h417, h488, h503, hc34, hlam, hphi, ht23, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, h503, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h416, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h413, h503, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p516_1, u2ehi2]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [h502, hlam, p516_1]
                                · have p516_0 := h516c.1
                                  have p516_1 := h516c.2.1
                                  have p516_2 := h516c.2.2.1
                                  have p516_3 := h516c.2.2.2
                                  linarith only [hlam, p516_0]
                              · linarith only [h0, h415, h417, h502, h514, h515, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                            · linarith only [h417, h502, h510, h514, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h413, h503, h505, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h413, h503, h504, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h415, h503, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h547 | h547
              · rcases m.htr 1 2 4 (by decide) (by decide) with h548 | h548
                · rcases m.htr 1 2 5 (by decide) (by decide) with h549 | h549
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                    · linarith only [h413, h417, h550, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
                      · linarith only [h0, h413, h552, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                        · linarith only [h413, h417, h547, h554, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h556 | h556
                          · linarith only [h413, h488, h547, h556, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h558 | h558
                            · linarith only [h415, h502, h558, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
                              · linarith only [h415, h502, h560, hc34, hlam, hphi, ht23, u2ehi3]
                              · linarith only [h414, h417, h560, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h413, h547, h549, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h413, h547, h548, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h415, h547, hc23, hlam, hphi, u2ehi3]
      · linarith only [h415, h416, hc25, hlam, hphi, u2ehi3]
    · linarith only [h414, h415, hc24, hlam, hphi, u2ehi2]
  · linarith only [h0, h413, h414, hlam]

end R2N4
