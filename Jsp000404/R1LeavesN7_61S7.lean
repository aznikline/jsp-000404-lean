import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_61S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3356000 in
set_option maxHeartbeats 3356000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_H_R_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h739 | h739
  · rcases m.htr 0 1 4 (by decide) (by decide) with h740 | h740
    · rcases m.htr 0 1 5 (by decide) (by decide) with h741 | h741
      · linarith only [h0, h741, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h743 | h743
        · rcases m.htr 0 2 4 (by decide) (by decide) with h744 | h744
          · rcases m.htr 0 2 5 (by decide) (by decide) with h745 | h745
            · rcases m.htr 0 3 4 (by decide) (by decide) with h746 | h746
              · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
                · linarith only [h0, h739, h747, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h749 | h749
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                        · linarith only [h739, h741, h751, h752, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h746, h747, h752, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h740, h745, h750, h751, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h740, h750, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h745, h749, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h758 | h758
                · linarith only [h746, h758, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h762 | h762
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h763 | h763
                        · linarith only [h739, h741, h762, h763, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h765 | h765
                          · linarith only [h740, h741, h758, h762, h763, h765, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h767 | h767
                            · linarith only [h740, h741, h765, h767, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h740, h741, h767, hc45, hlam, hphi, u4ehi1]
                      · linarith only [h0, h740, h745, h761, h762, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h745, h761, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h740, h760, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h773 | h773
              · rcases m.htr 0 3 5 (by decide) (by decide) with h774 | h774
                · linarith only [h0, h739, h774, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h776 | h776
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h777 | h777
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h778 | h778
                      · linarith only [h0, h740, h745, h778, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h740, h777, h778, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h740, h777, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h739, h773, h776, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h783 | h783
                · linarith only [h0, h740, h773, h783, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h787 | h787
                      · linarith only [h0, h740, h745, h786, h787, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h740, h786, h787, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h740, h786, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h740, h785, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h740, h744, hlam]
        · linarith only [h0, h739, h743, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h794 | h794
      · linarith only [h0, h794, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h796 | h796
        · rcases m.htr 0 2 4 (by decide) (by decide) with h797 | h797
          · rcases m.htr 0 2 5 (by decide) (by decide) with h798 | h798
            · rcases m.htr 0 3 4 (by decide) (by decide) with h799 | h799
              · linarith only [h739, h740, h799, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h801 | h801
                · linarith only [h799, h801, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h803 | h803
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h804 | h804
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                        · linarith only [h739, h740, h799, h804, h806, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                          · linarith only [h739, h740, h801, h806, h808, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                              · linarith only [h806, h810, h811, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h813 | h813
                                · linarith only [h739, h794, h803, h808, h813, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h815 | h815
                                  · linarith only [h797, h815, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h817 | h817
                                    · rcases h1bigk with h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c | h818c
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h0, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h794, h806, h810, hc13, hc34, hlam, hphi, p818_1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h740, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h794, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        rcases p818_3 (m.d 0 1) (by simp) with h824 | h824
                                        · linarith only [h824, hlam, p818_0]
                                        · rcases p818_3 (m.d 1 2) (by simp) with h826 | h826
                                          · rcases p818_3 (m.d 1 3) (by simp) with h827 | h827
                                            · linarith only [h803, h827, hlam]
                                            · rcases p818_3 (m.d 1 4) (by simp) with h829 | h829
                                              · linarith only [h804, h829, hlam]
                                              · linarith only [h740, h829, hlam]
                                          · linarith only [h826, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        rcases p818_3 (m.d 0 1) (by simp) with h834 | h834
                                        · linarith only [h0, h834, hlam]
                                        · linarith only [h739, h834, hlam]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h810, h815, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p818_1, u4ehi2]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p818_1, u5ehi1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h739, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h803, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h806, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h808, hlam, p818_1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h739, h806, hc13, hc34, hlam, hphi, p818_1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h804, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        rcases p818_3 (m.d 0 1) (by simp) with h846 | h846
                                        · linarith only [h740, h846, hlam]
                                        · linarith only [h739, h846, hlam]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h739, h794, h803, h806, hc23, hc34, hlam, hphi, p818_1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h739, h803, h808, hc23, hc35, hlam, hphi, p818_1]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h805, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        rcases p818_3 (m.d 0 1) (by simp) with h853 | h853
                                        · linarith only [h794, h853, hlam]
                                        · linarith only [h739, h853, hlam]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [h810, hlam, p818_0]
                                      · have p818_0 := h818c.1
                                        have p818_1 := h818c.2.1
                                        have p818_2 := h818c.2.2.1
                                        have p818_3 := h818c.2.2.2
                                        linarith only [hlam, p818_0]
                                    · linarith only [h806, h810, h817, hlam]
                            · linarith only [h739, h740, h803, h810, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h798, h805, hlam]
                    · linarith only [h0, h798, h804, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h798, h803, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h863 | h863
              · linarith only [h739, h740, h863, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h865 | h865
                · linarith only [h739, h740, h797, h798, h865, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h867 | h867
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h868 | h868
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h869 | h869
                      · linarith only [h797, h798, h869, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h871 | h871
                        · linarith only [h0, h739, h863, h869, h871, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h873 | h873
                          · linarith only [h739, h740, h865, h868, h869, h873, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h875 | h875
                            · linarith only [h868, h869, h875, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h739, h740, h867, h875, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h739, h797, h867, h868, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h796, h867, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h880 | h880
            · linarith only [h797, h880, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h882 | h882
              · linarith only [h0, h739, h797, h882, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h884 | h884
                · linarith only [h0, h739, h797, h884, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
                        · linarith only [h0, h739, h797, h882, h887, h889, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                          · linarith only [h0, h739, h797, h884, h887, h891, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                              · linarith only [h889, h893, h894, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
                                · linarith only [h0, h739, h797, h886, h887, h896, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h898 | h898
                                  · linarith only [h887, h898, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h797, h893, h898, hc01, hc14, hlam, hphi]
                            · linarith only [h739, h740, h886, h893, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h739, h797, h886, h887, h888, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h903 | h903
                      · linarith only [h887, h903, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h905 | h905
                        · linarith only [h0, h739, h887, h905, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h907 | h907
                          · linarith only [h0, h739, h887, h907, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h909 | h909
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h910 | h910
                              · linarith only [h0, h739, h886, h887, h905, h909, h910, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · linarith only [h0, h739, h886, h887, h910, hc23, hc34, hlam, hphi]
                            · linarith only [h739, h740, h886, h909, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h739, h796, h797, h886, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h739, h796, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h916 | h916
    · rcases m.htr 0 1 5 (by decide) (by decide) with h917 | h917
      · linarith only [h739, h917, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h919 | h919
        · rcases m.htr 0 2 4 (by decide) (by decide) with h920 | h920
          · rcases m.htr 0 2 5 (by decide) (by decide) with h921 | h921
            · rcases m.htr 0 3 4 (by decide) (by decide) with h922 | h922
              · rcases m.htr 0 3 5 (by decide) (by decide) with h923 | h923
                · rcases m.htr 1 2 3 (by decide) (by decide) with h924 | h924
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h925 | h925
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h926 | h926
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h927 | h927
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h928 | h928
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h929 | h929
                            · linarith only [h916, h917, h924, h928, h929, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · linarith only [h916, h917, h929, hc45, hlam, hphi, u4ehi1]
                          · linarith only [h739, h916, h919, h923, h925, h928, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h739, h916, h925, h927, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h916, h925, h926, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h739, h916, h924, h925, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h916, h919, h924, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h939 | h939
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h940 | h940
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h941 | h941
                          · linarith only [h739, h916, h923, h938, h941, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                          · linarith only [h739, h916, h938, h941, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h739, h916, h938, h940, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h916, h938, h939, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h739, h916, h937, h938, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h919, h937, hlam]
              · linarith only [h739, h916, h922, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h949 | h949
              · rcases m.htr 0 3 5 (by decide) (by decide) with h950 | h950
                · linarith only [h919, h921, h950, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h952 | h952
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h953 | h953
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h954 | h954
                      · linarith only [h919, h921, h949, h954, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h916, h953, h954, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · linarith only [h739, h916, h952, h953, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                  · linarith only [h919, h921, h952, hc12, hc25, hlam, hphi]
              · linarith only [h739, h916, h949, hlam]
          · linarith only [h0, h916, h920, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h961 | h961
          · rcases m.htr 0 2 5 (by decide) (by decide) with h962 | h962
            · linarith only [h919, h962, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h964 | h964
              · rcases m.htr 0 3 5 (by decide) (by decide) with h965 | h965
                · rcases m.htr 1 2 3 (by decide) (by decide) with h966 | h966
                  · linarith only [h919, h961, h966, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h916, h966, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
                  · linarith only [h0, h916, h919, h969, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h0, h916, h969, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · linarith only [h739, h916, h964, hlam]
          · linarith only [h0, h916, h961, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h974 | h974
      · linarith only [h0, h974, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h976 | h976
        · rcases m.htr 0 2 4 (by decide) (by decide) with h977 | h977
          · rcases m.htr 0 2 5 (by decide) (by decide) with h978 | h978
            · rcases m.htr 0 3 4 (by decide) (by decide) with h979 | h979
              · rcases m.htr 0 3 5 (by decide) (by decide) with h980 | h980
                · rcases m.htr 1 2 3 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h985 | h985
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h986 | h986
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h987 | h987
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h988 | h988
                                · linarith only [h976, h988, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · linarith only [h980, h987, h988, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                                · linarith only [h976, h991, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h993 | h993
                                  · linarith only [h979, h987, h993, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                                    · linarith only [h739, h979, h981, h993, h995, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                    · rcases h1bigk with h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c | h997c
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h0, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h739, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h916, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h974, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        rcases p997_3 (m.d 0 1) (by simp) with h1003 | h1003
                                        · linarith only [h1003, hlam, p997_0]
                                        · rcases p997_3 (m.d 1 2) (by simp) with h1005 | h1005
                                          · rcases p997_3 (m.d 1 3) (by simp) with h1006 | h1006
                                            · linarith only [h1006, h981, hlam]
                                            · linarith only [h1006, h739, hlam]
                                          · linarith only [h1005, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h739, hc01, hc12, hlam, hphi, p997_1]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h986, h987, h995, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p997_1]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h974, hc12, hlam, hphi, ht01, ht0b, ht5b, p997_1, u5ehi0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        rcases p997_3 (m.d 0 1) (by simp) with h1014 | h1014
                                        · linarith only [h1014, hlam, p997_0]
                                        · rcases p997_3 (m.d 1 2) (by simp) with h1016 | h1016
                                          · rcases p997_3 (m.d 1 3) (by simp) with h1017 | h1017
                                            · rcases p997_3 (m.d 1 4) (by simp) with h1018 | h1018
                                              · linarith only [h1018, h984, hlam]
                                              · linarith only [h1018, h916, hlam]
                                            · linarith only [h1017, hlam, p997_0]
                                          · linarith only [h0, h1016, hlam]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h981, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h986, h987, h995, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p997_1]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h974, h980, h981, h991, hc12, hlam, hphi, ht01, ht0b, ht5b, p997_1, u5ehi2]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        rcases p997_3 (m.d 0 1) (by simp) with h1027 | h1027
                                        · linarith only [h1027, hlam, p997_0]
                                        · rcases p997_3 (m.d 1 2) (by simp) with h1029 | h1029
                                          · rcases p997_3 (m.d 1 3) (by simp) with h1030 | h1030
                                            · rcases p997_3 (m.d 1 4) (by simp) with h1031 | h1031
                                              · rcases p997_3 (m.d 1 5) (by simp) with h1032 | h1032
                                                · linarith only [h1032, h986, hlam]
                                                · linarith only [h1032, h974, hlam]
                                              · linarith only [h1031, hlam, p997_0]
                                            · linarith only [h1030, h739, hlam]
                                          · linarith only [h0, h1029, hlam]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h982, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h984, hlam, p997_1]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h974, h980, h991, hc14, hlam, hphi, ht01, ht0b, ht5b, p997_1, u5ehi2]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        rcases p997_3 (m.d 0 1) (by simp) with h1042 | h1042
                                        · linarith only [h1042, hlam, p997_0]
                                        · rcases p997_3 (m.d 1 2) (by simp) with h1044 | h1044
                                          · rcases p997_3 (m.d 1 3) (by simp) with h1045 | h1045
                                            · rcases p997_3 (m.d 1 4) (by simp) with h1046 | h1046
                                              · rcases p997_3 (m.d 1 5) (by simp) with h1047 | h1047
                                                · rcases h2bigk with h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h0, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    rcases p1048_3 (m.d 0 2) (by simp) with h1051 | h1051
                                                    · rcases p1048_3 (m.d 1 2) (by simp) with h1052 | h1052
                                                      · rcases p1048_3 (m.d 2 3) (by simp) with h1053 | h1053
                                                        · linarith only [h1053, hlam, p1048_0]
                                                        · rcases p1048_3 (m.d 2 4) (by simp) with h1055 | h1055
                                                          · linarith only [h1055, h977, hlam]
                                                          · linarith only [h1055, h987, hlam]
                                                      · linarith only [h1052, h981, hlam]
                                                    · linarith only [h1051, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    rcases p1048_3 (m.d 0 2) (by simp) with h1060 | h1060
                                                    · rcases p1048_3 (m.d 1 2) (by simp) with h1061 | h1061
                                                      · rcases p1048_3 (m.d 2 3) (by simp) with h1062 | h1062
                                                        · linarith only [h1062, h976, hlam]
                                                        · rcases p1048_3 (m.d 2 4) (by simp) with h1064 | h1064
                                                          · linarith only [h1064, hlam, p1048_0]
                                                          · rcases p1048_3 (m.d 2 5) (by simp) with h1066 | h1066
                                                            · linarith only [h1066, h978, hlam]
                                                            · linarith only [h1066, h993, hlam]
                                                      · linarith only [h1061, h982, hlam]
                                                    · linarith only [h1060, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hc02, hlam, hphi, ht0b, ht5b, p1048_1, u5ehi2]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h976, h980, h991, hc12, hlam, hphi, ht01, ht0b, ht5b, p1048_1, u5ehi2]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h981, h984, h986, h987, h995, hlam, p1048_2]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    rcases p1048_3 (m.d 0 2) (by simp) with h1075 | h1075
                                                    · linarith only [h0, h1075, hlam]
                                                    · linarith only [h1075, h977, hlam]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1048_1, u5ehi2]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h976, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h981, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h987, hlam, p1048_1]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h991, hlam, p1048_1]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h977, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h982, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h981, h984, h986, h987, h995, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1048_1]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h993, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h978, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h983, hlam, p1048_0]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    rcases p1048_3 (m.d 0 2) (by simp) with h1091 | h1091
                                                    · rcases p1048_3 (m.d 1 2) (by simp) with h1092 | h1092
                                                      · rcases p1048_3 (m.d 2 3) (by simp) with h1093 | h1093
                                                        · linarith only [h1093, h991, hlam]
                                                        · rcases p1048_3 (m.d 2 4) (by simp) with h1095 | h1095
                                                          · linarith only [h1095, h993, hlam]
                                                          · linarith only [h1095, h987, hlam]
                                                      · linarith only [h1092, h981, hlam]
                                                    · linarith only [h1091, h976, hlam]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [h976, h980, h991, hc02, hlam, hphi, ht0b, ht45, ht5b, p1048_1, u4ehi2]
                                                  · have p1048_0 := h1048c.1
                                                    have p1048_1 := h1048c.2.1
                                                    have p1048_2 := h1048c.2.2.1
                                                    have p1048_3 := h1048c.2.2.2
                                                    linarith only [hlam, p1048_0]
                                                · linarith only [h1047, hlam, p997_0]
                                              · linarith only [h1046, h916, hlam]
                                            · linarith only [h1045, h739, hlam]
                                          · linarith only [h0, h1044, hlam]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h983, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h985, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [h986, hlam, p997_0]
                                      · have p997_0 := h997c.1
                                        have p997_1 := h997c.2.1
                                        have p997_2 := h997c.2.2.1
                                        have p997_3 := h997c.2.2.2
                                        linarith only [hlam, p997_0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
                                · linarith only [h0, h1111, h976, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · linarith only [h0, h1110, h1111, h976, h980, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1114 | h1114
                                · linarith only [h1110, h1114, h979, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                                  · linarith only [h1116, h916, h986, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1118 | h1118
                                    · linarith only [h1118, h916, h979, h986, hlam]
                                    · rcases h1bigk with h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c | h1120c
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h0, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h739, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h916, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h974, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        rcases p1120_3 (m.d 0 1) (by simp) with h1126 | h1126
                                        · linarith only [h1126, hlam, p1120_0]
                                        · rcases p1120_3 (m.d 1 2) (by simp) with h1128 | h1128
                                          · rcases p1120_3 (m.d 1 3) (by simp) with h1129 | h1129
                                            · linarith only [h1129, h981, hlam]
                                            · linarith only [h1129, h739, hlam]
                                          · linarith only [h1128, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h739, hc01, hc12, hlam, hphi, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h916, hc01, hc12, hlam, hphi, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1120_1, u5ehi1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        rcases p1120_3 (m.d 0 1) (by simp) with h1137 | h1137
                                        · linarith only [h1137, hlam, p1120_0]
                                        · rcases p1120_3 (m.d 1 2) (by simp) with h1139 | h1139
                                          · rcases p1120_3 (m.d 1 3) (by simp) with h1140 | h1140
                                            · rcases p1120_3 (m.d 1 4) (by simp) with h1141 | h1141
                                              · linarith only [h1141, h984, hlam]
                                              · linarith only [h1141, h916, hlam]
                                            · linarith only [h1140, hlam, p1120_0]
                                          · linarith only [h0, h1139, hlam]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h981, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h916, hc01, hc13, hlam, hphi, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h1114, h974, h980, h981, hc12, hlam, hphi, ht01, ht0b, ht5b, p1120_1, u5ehi2]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h986, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h982, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h984, hlam, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h986, hlam, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        rcases p1120_3 (m.d 0 1) (by simp) with h1155 | h1155
                                        · linarith only [h1155, hlam, p1120_0]
                                        · rcases p1120_3 (m.d 1 2) (by simp) with h1157 | h1157
                                          · rcases p1120_3 (m.d 1 3) (by simp) with h1158 | h1158
                                            · rcases p1120_3 (m.d 1 4) (by simp) with h1159 | h1159
                                              · linarith only [h1159, h986, hlam]
                                              · linarith only [h1159, h916, hlam]
                                            · linarith only [h1158, h739, hlam]
                                          · linarith only [h0, h1157, hlam]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h983, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h985, hlam, p1120_0]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [h916, hc01, hc15, hlam, hphi, p1120_1]
                                      · have p1120_0 := h1120c.1
                                        have p1120_1 := h1120c.2.1
                                        have p1120_2 := h1120c.2.2.1
                                        have p1120_3 := h1120c.2.2.2
                                        linarith only [hlam, p1120_0]
                          · linarith only [h739, h980, h985, hlam]
                        · linarith only [h739, h980, h984, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · linarith only [h0, h976, h980, h983, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · linarith only [h0, h976, h977, h980, h982, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h976, h980, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1175 | h1175
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1176 | h1176
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1177 | h1177
                          · linarith only [h1173, h1177, h979, h980, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1179 | h1179
                            · linarith only [h1176, h1177, h1179, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1181 | h1181
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1182 | h1182
                                · linarith only [h1182, h976, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1184 | h1184
                                  · linarith only [h1179, h1184, h916, h977, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1186 | h1186
                                    · linarith only [h1179, h1186, h916, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1177, h1181, h1186, h739, h976, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h1177, h1181, h739, h979, hc23, hc35, hlam, hphi]
                        · linarith only [h1176, h739, h979, hlam]
                      · linarith only [h0, h1175, h978, hlam]
                    · linarith only [h0, h1174, h916, h977, h978, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h1173, h978, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1194 | h1194
                · linarith only [h1194, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1196 | h1196
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1197 | h1197
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1199 | h1199
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1200 | h1200
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1201 | h1201
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1202 | h1202
                              · linarith only [h1202, h976, h979, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1204 | h1204
                                · linarith only [h1194, h1196, h1199, h1204, h976, h979, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1206 | h1206
                                  · linarith only [h1206, h977, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1208 | h1208
                                    · linarith only [h1196, h1199, h1206, h1208, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                    · linarith only [h1196, h1199, h1201, h1208, h739, h979, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                              · linarith only [h1211, h976, h979, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1213 | h1213
                                · linarith only [h1194, h1213, h976, h978, h979, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1215 | h1215
                                  · linarith only [h1199, h1201, h1215, h739, h979, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                                    · linarith only [h1199, h1201, h1217, hlam]
                                    · rcases h1bigk with h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c | h1219c
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h0, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h739, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h916, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h974, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        rcases p1219_3 (m.d 0 1) (by simp) with h1225 | h1225
                                        · linarith only [h1225, hlam, p1219_0]
                                        · rcases p1219_3 (m.d 1 2) (by simp) with h1227 | h1227
                                          · rcases p1219_3 (m.d 1 3) (by simp) with h1228 | h1228
                                            · linarith only [h1196, h1228, hlam]
                                            · linarith only [h1228, h739, hlam]
                                          · linarith only [h1227, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h739, hc01, hc12, hlam, hphi, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1199, h739, h979, hc01, hc12, hlam, hphi, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1219_1, u5ehi1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        rcases p1219_3 (m.d 0 1) (by simp) with h1236 | h1236
                                        · linarith only [h1236, hlam, p1219_0]
                                        · rcases p1219_3 (m.d 1 2) (by simp) with h1238 | h1238
                                          · rcases p1219_3 (m.d 1 3) (by simp) with h1239 | h1239
                                            · rcases p1219_3 (m.d 1 4) (by simp) with h1240 | h1240
                                              · linarith only [h1199, h1240, hlam]
                                              · linarith only [h1240, h916, hlam]
                                            · linarith only [h1239, hlam, p1219_0]
                                          · linarith only [h0, h1238, hlam]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1196, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1199, h739, h979, hc01, hc13, hlam, hphi, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1194, h1196, h1200, h978, hc12, hlam, hphi, ht01, ht0b, ht5b, p1219_1, u5ehi2]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1201, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1197, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1199, hlam, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1201, hlam, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        rcases p1219_3 (m.d 0 1) (by simp) with h1254 | h1254
                                        · linarith only [h1254, hlam, p1219_0]
                                        · rcases p1219_3 (m.d 1 2) (by simp) with h1256 | h1256
                                          · rcases p1219_3 (m.d 1 3) (by simp) with h1257 | h1257
                                            · rcases p1219_3 (m.d 1 4) (by simp) with h1258 | h1258
                                              · linarith only [h1201, h1258, hlam]
                                              · linarith only [h1258, h916, hlam]
                                            · linarith only [h1257, h739, hlam]
                                          · linarith only [h0, h1256, hlam]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1198, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h1200, hlam, p1219_0]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [h916, hc01, hc15, hlam, hphi, p1219_1]
                                      · have p1219_0 := h1219c.1
                                        have p1219_1 := h1219c.2.1
                                        have p1219_2 := h1219c.2.2.1
                                        have p1219_3 := h1219c.2.2.2
                                        linarith only [hlam, p1219_0]
                          · linarith only [h1199, h1200, h739, h979, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1268 | h1268
                          · linarith only [h1199, h1268, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1270 | h1270
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1271 | h1271
                              · linarith only [h1199, h1270, h1271, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1273 | h1273
                                · linarith only [h1199, h1273, h739, h976, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1275 | h1275
                                  · linarith only [h0, h1275, h977, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1277 | h1277
                                    · rcases h1bigk with h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c | h1278c
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h0, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h739, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h916, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h974, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        rcases p1278_3 (m.d 0 1) (by simp) with h1284 | h1284
                                        · linarith only [h1284, hlam, p1278_0]
                                        · rcases p1278_3 (m.d 1 2) (by simp) with h1286 | h1286
                                          · rcases p1278_3 (m.d 1 3) (by simp) with h1287 | h1287
                                            · linarith only [h1196, h1287, hlam]
                                            · linarith only [h1287, h739, hlam]
                                          · linarith only [h1286, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h739, hc01, hc12, hlam, hphi, p1278_1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1270, h1275, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1278_1, u4ehi2]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1278_1, u5ehi1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1199, hc01, hc34, hlam, hphi, ht12, ht23, p1278_1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1196, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1199, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1268, hlam, p1278_1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        rcases p1278_3 (m.d 0 1) (by simp) with h1300 | h1300
                                        · linarith only [h1300, hlam, p1278_0]
                                        · rcases p1278_3 (m.d 1 2) (by simp) with h1302 | h1302
                                          · rcases p1278_3 (m.d 1 3) (by simp) with h1303 | h1303
                                            · linarith only [h1199, h1303, hlam]
                                            · linarith only [h1303, h739, hlam]
                                          · linarith only [h0, h1302, hlam]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1197, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h739, hc01, hc14, hlam, hphi, p1278_1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1199, h974, h978, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1278_1, u5ehi2]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        rcases p1278_3 (m.d 0 1) (by simp) with h1311 | h1311
                                        · linarith only [h1311, hlam, p1278_0]
                                        · rcases p1278_3 (m.d 1 2) (by simp) with h1313 | h1313
                                          · rcases p1278_3 (m.d 1 3) (by simp) with h1314 | h1314
                                            · linarith only [h1268, h1314, hlam]
                                            · linarith only [h1314, h739, hlam]
                                          · linarith only [h0, h1313, hlam]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1198, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h739, hc01, hc15, hlam, hphi, p1278_1]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [h1270, hlam, p1278_0]
                                      · have p1278_0 := h1278c.1
                                        have p1278_1 := h1278c.2.1
                                        have p1278_2 := h1278c.2.2.1
                                        have p1278_3 := h1278c.2.2.2
                                        linarith only [hlam, p1278_0]
                                    · linarith only [h1199, h1277, h739, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1323 | h1323
                              · linarith only [h1199, h1323, h739, h976, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1325 | h1325
                                · linarith only [h0, h1325, h976, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1327 | h1327
                                  · linarith only [h1270, h1327, h916, h977, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1329 | h1329
                                    · linarith only [h1270, h1329, h916, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h1199, h1329, h739, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1198, h978, hlam]
                    · linarith only [h0, h1197, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h0, h1196, h976, h978, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1335 | h1335
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1336 | h1336
                · linarith only [h1336, h976, h978, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1338 | h1338
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1339 | h1339
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1340 | h1340
                      · linarith only [h1340, h977, h978, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1342 | h1342
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1343 | h1343
                          · linarith only [h1335, h1336, h1343, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1345 | h1345
                            · linarith only [h1338, h1340, h1342, h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1347 | h1347
                              · linarith only [h0, h1340, h1347, h976, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                              · linarith only [h1335, h1336, h1347, hc23, hc35, hlam, hphi]
                        · linarith only [h1335, h1336, h1342, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1339, h977, hlam]
                  · linarith only [h0, h1338, h976, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1353 | h1353
                · linarith only [h1335, h1353, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1356 | h1356
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1357 | h1357
                      · linarith only [h1357, h977, h978, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1359 | h1359
                        · linarith only [h1335, h1355, h1357, h1359, h739, hc01, hc25, hlam, hphi, ht12]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1361 | h1361
                          · linarith only [h1353, h1356, h1357, h1359, h1361, h977, h978, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1363 | h1363
                            · linarith only [h1356, h1357, h1363, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1365 | h1365
                              · linarith only [h1359, h1365, h739, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1367 | h1367
                                · linarith only [h1361, h1365, h1367, h739, h977, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1369 | h1369
                                  · linarith only [h0, h1357, h1363, h1367, h1369, h977, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                                  · linarith only [h0, h1357, h1369, h977, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h0, h1356, h977, hlam]
                  · linarith only [h0, h1355, h976, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1374 | h1374
            · linarith only [h1374, h977, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1376 | h1376
              · linarith only [h1376, h976, h977, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1378 | h1378
                · linarith only [h1378, h976, h977, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1380 | h1380
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1381 | h1381
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1382 | h1382
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1383 | h1383
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1384 | h1384
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1385 | h1385
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1386 | h1386
                              · linarith only [h1376, h1381, h1386, h976, h977, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1388 | h1388
                                · linarith only [h1378, h1380, h1383, h1386, h1388, h976, h977, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1390 | h1390
                                  · linarith only [h1380, h1383, h1386, h1390, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · linarith only [h1385, h1390, h976, h977, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1381, h1385, h976, h977, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1376, h1383, h1384, h739, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1395 | h1395
                          · linarith only [h1378, h1383, h1395, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1397 | h1397
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1398 | h1398
                              · linarith only [h1381, h1383, h1398, h976, h977, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1400 | h1400
                                · linarith only [h1381, h1400, h976, h977, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1402 | h1402
                                  · linarith only [h1381, h1402, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · linarith only [h1397, h1402, h976, h977, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h1381, h1397, h976, h977, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h1381, h1382, h976, h977, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1407 | h1407
                      · linarith only [h1381, h1407, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1409 | h1409
                        · linarith only [h1376, h1380, h1381, h1409, h739, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1411 | h1411
                          · linarith only [h1409, h1411, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1414 | h1414
                              · linarith only [h1409, h1413, h1414, h976, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1416 | h1416
                                · linarith only [h0, h1381, h1414, h1416, h976, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1418 | h1418
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1419 | h1419
                                    · rcases h1bigk with h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c | h1420c
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h0, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h739, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h916, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h974, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1407, h1414, h1418, hc01, hc34, hlam, hphi, ht12, ht23, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1407, h1414, h1418, h739, hc03, hc34, hlam, hphi, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1381, hlam, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1407, hlam, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1380, h1407, h1414, h1418, hc01, hc34, hlam, hphi, ht12, ht23, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1380, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1409, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1411, hlam, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        rcases p1420_3 (m.d 0 1) (by simp) with h1436 | h1436
                                        · linarith only [h1436, hlam, p1420_0]
                                        · rcases p1420_3 (m.d 1 2) (by simp) with h1438 | h1438
                                          · linarith only [h1381, h1438, hlam]
                                          · linarith only [h0, h1438, hlam]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h0, h1381, h1414, h976, hc23, hc34, hlam, hphi, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1381, h1414, h739, hc01, hc34, hlam, hphi, ht12, ht23, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1381, h1414, h974, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1420_1, u5ehi0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        rcases p1420_3 (m.d 0 1) (by simp) with h1445 | h1445
                                        · linarith only [h1445, hlam, p1420_0]
                                        · rcases p1420_3 (m.d 1 2) (by simp) with h1447 | h1447
                                          · linarith only [h1407, h1447, hlam]
                                          · linarith only [h0, h1447, hlam]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1380, h739, hc01, hc15, hlam, hphi, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h739, hc01, hc15, hlam, hphi, p1420_1]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [h1413, hlam, p1420_0]
                                      · have p1420_0 := h1420c.1
                                        have p1420_1 := h1420c.2.1
                                        have p1420_2 := h1420c.2.2.1
                                        have p1420_3 := h1420c.2.2.2
                                        linarith only [hlam, p1420_0]
                                    · linarith only [h1414, h1419, h976, h977, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h1381, h1413, h1418, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1456 | h1456
                              · linarith only [h1409, h1456, h739, h976, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1458 | h1458
                                · linarith only [h1458, h976, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1460 | h1460
                                  · linarith only [h1380, h1381, h1413, h1456, h1460, h739, hc01, hc34, hlam, hphi, ht12, ht23]
                                  · linarith only [h1460, h976, h977, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1380, h976, h977, hc12, hc24, hlam, hphi]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1464 | h1464
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1465 | h1465
            · linarith only [h1465, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1467 | h1467
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                  · linarith only [h1464, h1469, h976, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1471 | h1471
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                      · linarith only [h1464, h1465, h1469, h1472, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1474 | h1474
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1475 | h1475
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                            · linarith only [h1469, h1471, h1476, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1478 | h1478
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1479 | h1479
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1480 | h1480
                                  · linarith only [h1464, h1476, h1480, h916, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h1464, h1472, h1478, h1480, hc45, hlam, hphi, u4ehi3]
                                · linarith only [h1468, h1469, h1479, h739, hlam]
                              · linarith only [h1468, h1469, h1478, h739, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h1468, h1475, h739, hlam]
                        · linarith only [h1467, h1468, h1474, h739, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · linarith only [h0, h1464, h1471, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1488 | h1488
                  · linarith only [h1464, h1488, h976, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1490 | h1490
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1491 | h1491
                      · linarith only [h1464, h1465, h1491, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1493 | h1493
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                          · linarith only [h1467, h1468, h1488, h1494, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                            · linarith only [h1488, h1490, h1494, h1496, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1498 | h1498
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                                · linarith only [h0, h1488, h1494, h1499, hc01, hc23, hlam, hphi, ht12]
                                · linarith only [h1464, h1498, h1499, h976, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h1464, h1488, h1498, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1464, h1467, h1488, h1493, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1464, h1490, hlam]
              · linarith only [h1464, h1467, h976, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1506 | h1506
            · linarith only [h1464, h1506, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1508 | h1508
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1509 | h1509
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1510 | h1510
                  · linarith only [h1509, h1510, h976, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1512 | h1512
                    · linarith only [h0, h1464, h1510, h1512, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1514 | h1514
                      · linarith only [h1506, h1510, h1514, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1516 | h1516
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1517 | h1517
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1518 | h1518
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1519 | h1519
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1520 | h1520
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1521 | h1521
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1522 | h1522
                                    · linarith only [h1508, h1522, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                    · rcases h1bigk with h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h0, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h739, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h916, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h974, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1514, h1519, h1521, hc01, hc23, hlam, hphi, ht12, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1510, hlam, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1512, hlam, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1514, hlam, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        rcases p1524_3 (m.d 0 1) (by simp) with h1535 | h1535
                                        · linarith only [h1535, hlam, p1524_0]
                                        · rcases p1524_3 (m.d 1 2) (by simp) with h1537 | h1537
                                          · linarith only [h1510, h1537, hlam]
                                          · linarith only [h0, h1537, hlam]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h0, hc01, hc13, hlam, hphi, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1518, hc13, hlam, hphi, ht01, ht0b, ht5b, p1524_1, u5ehi1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1509, h1510, h974, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1524_1, u5ehi3]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        rcases p1524_3 (m.d 0 1) (by simp) with h1544 | h1544
                                        · linarith only [h1544, hlam, p1524_0]
                                        · rcases p1524_3 (m.d 1 2) (by simp) with h1546 | h1546
                                          · linarith only [h1512, h1546, hlam]
                                          · linarith only [h0, h1546, hlam]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h0, hc01, hc14, hlam, hphi, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1516, hlam, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1509, h1512, h1519, h974, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1524_1, u5ehi3]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        rcases p1524_3 (m.d 0 1) (by simp) with h1553 | h1553
                                        · linarith only [h1553, hlam, p1524_0]
                                        · rcases p1524_3 (m.d 1 2) (by simp) with h1555 | h1555
                                          · linarith only [h1514, h1555, hlam]
                                          · linarith only [h0, h1555, hlam]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h0, hc01, hc15, hlam, hphi, p1524_1]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1517, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [h1518, hlam, p1524_0]
                                      · have p1524_0 := h1524c.1
                                        have p1524_1 := h1524c.2.1
                                        have p1524_2 := h1524c.2.2.1
                                        have p1524_3 := h1524c.2.2.2
                                        linarith only [hlam, p1524_0]
                                  · linarith only [h0, h1512, h1521, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h1509, h1510, h1520, h739, hlam]
                              · linarith only [h1508, h1509, h1510, h1519, h739, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1565 | h1565
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1566 | h1566
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1567 | h1567
                                  · linarith only [h1518, h1565, h1567, h916, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h1512, h1567, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h1509, h1566, h739, h976, hc01, hc13, hlam, hphi]
                              · linarith only [h1508, h1509, h1510, h1565, h739, h916, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h1509, h1517, h739, hlam]
                        · linarith only [h1508, h1516, h739, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1574 | h1574
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1575 | h1575
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1576 | h1576
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1577 | h1577
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1578 | h1578
                          · linarith only [h1508, h1509, h1578, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1580 | h1580
                            · linarith only [h1577, h1578, h1580, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1582 | h1582
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                                · linarith only [h1578, h1583, h739, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1585 | h1585
                                  · linarith only [h1575, h1580, h1585, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1587 | h1587
                                    · linarith only [h1464, h1508, h1575, h1580, h1587, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                    · linarith only [h1508, h1574, h1578, h1587, h976, hc45, hlam, hphi, u4ehi3]
                              · linarith only [h1508, h1582, h976, hlam]
                        · linarith only [h1508, h1574, h1577, h976, hlam]
                      · linarith only [h1508, h1574, h1576, h976, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h1508, h1574, h1575, h976, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1594 | h1594
                    · linarith only [h0, h1464, h1574, h1594, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1596 | h1596
                      · linarith only [h1574, h1596, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1598 | h1598
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1599 | h1599
                          · linarith only [h1508, h1509, h1599, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1601 | h1601
                            · linarith only [h1598, h1599, h1601, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1604 | h1604
                                · linarith only [h1508, h1599, h1604, h739, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h1574, h1604, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h1508, h1574, h1603, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · linarith only [h1508, h1509, h1598, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1609 | h1609
                · linarith only [h1508, h1609, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1611 | h1611
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1612 | h1612
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1613 | h1613
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1614 | h1614
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1615 | h1615
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1616 | h1616
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1617 | h1617
                              · linarith only [h1508, h1611, h1617, h739, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h1611, h1614, h1617, h976, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1620 | h1620
                              · linarith only [h0, h1508, h1611, h1620, h976, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h1614, h1616, h1620, h976, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h0, h1508, h1614, h1615, h976, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1624 | h1624
                          · linarith only [h1614, h1624, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1626 | h1626
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1627 | h1627
                              · linarith only [h1614, h1627, h739, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1629 | h1629
                                · linarith only [h1609, h1611, h1629, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1631 | h1631
                                  · linarith only [h1612, h1631, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h1464, h1626, h1631, hc01, hc14, hlam, hphi]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1634 | h1634
                              · linarith only [h1611, h1614, h1626, h1634, hc45, hlam, hphi, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1636 | h1636
                                · linarith only [h1611, h1614, h1626, h1636, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1638 | h1638
                                  · linarith only [h1614, h1626, h1638, h739, hc01, hc24, hlam, hphi, ht12]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1640 | h1640
                                    · linarith only [h0, h1611, h1614, h1626, h1640, h976, hc01, hc34, hlam, hphi, ht12, ht23]
                                    · linarith only [h0, h1611, h1614, h1640, h976, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h1611, h1613, h976, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1611, h1612, h976, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1645 | h1645
                    · linarith only [h0, h1464, h1611, h1645, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1647 | h1647
                      · linarith only [h1611, h1647, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1649 | h1649
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1650 | h1650
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1651 | h1651
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1652 | h1652
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1653 | h1653
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1654 | h1654
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1655 | h1655
                                    · linarith only [h1649, h1655, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                    · linarith only [h0, h1508, h1651, h1655, h976, hc01, hc14, hlam, hphi]
                                  · linarith only [h1645, h1651, h1654, hlam]
                                · linarith only [h1645, h1651, h1652, h1653, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                              · linarith only [h1611, h1650, h1652, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1661 | h1661
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1662 | h1662
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1663 | h1663
                                  · linarith only [h0, h1645, h1651, h1661, h1663, hc01, hc23, hlam, hphi, ht12]
                                  · linarith only [h0, h1645, h1663, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                                · linarith only [h0, h1611, h1662, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h1611, h1650, h1661, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h0, h1508, h1649, h1650, h976, hc01, hc35, hlam, hphi, ht12, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1669 | h1669
                          · linarith only [h1649, h1669, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1671 | h1671
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1672 | h1672
                              · linarith only [h1649, h1672, h739, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1611, h1672, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1675 | h1675
                              · linarith only [h0, h1611, h1649, h1675, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h0, h1611, h1675, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 3356000 in
set_option maxHeartbeats 3356000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_R_H_R (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have h5ehi := hb5.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_H_R_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_R_H_R_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
