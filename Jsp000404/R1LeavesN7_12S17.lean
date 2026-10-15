import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_12S9
import Jsp000404.R1LeavesN7_12S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11264000 in
set_option maxHeartbeats 11264000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s7 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h6794 | h6794
  · rcases m.htr 0 1 4 (by decide) (by decide) with h6795 | h6795
    · rcases m.htr 0 1 5 (by decide) (by decide) with h6796 | h6796
      · rcases m.htr 0 2 3 (by decide) (by decide) with h6797 | h6797
        · rcases m.htr 0 2 4 (by decide) (by decide) with h6798 | h6798
          · rcases m.htr 0 2 5 (by decide) (by decide) with h6799 | h6799
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6800 | h6800
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6801 | h6801
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6802 | h6802
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6803 | h6803
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6804 | h6804
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6805 | h6805
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6806 | h6806
                          · linarith only [h0, h6794, h6806, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6808 | h6808
                            · linarith only [h0, h6796, h6805, h6806, h6808, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6810 | h6810
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6811 | h6811
                                · linarith only [h6802, h6806, h6811, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6813 | h6813
                                  · linarith only [h6803, h6808, h6813, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6815 | h6815
                                    · linarith only [h6802, h6806, h6808, h6810, h6815, hlam]
                                    · linarith only [h0, h6794, h6800, h6801, h6802, h6806, h6810, h6815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6805, h6806, h6810, hc23, hc35, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6819 | h6819
                          · linarith only [h0, h6794, h6819, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6821 | h6821
                            · linarith only [h0, h6794, h6800, h6805, h6821, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6823 | h6823
                              · linarith only [h0, h6794, h6800, h6801, h6802, h6805, h6821, h6823, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6825 | h6825
                                · linarith only [h0, h6794, h6800, h6801, h6802, h6805, h6819, h6821, h6825, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6827 | h6827
                                  · linarith only [h6803, h6821, h6827, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6829 | h6829
                                    · linarith only [h0, h6794, h6800, h6805, h6821, h6829, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                    · linarith only [h0, h6794, h6800, h6801, h6802, h6805, h6829, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h6794, h6800, h6801, h6804, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h6794, h6800, h6801, h6803, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h6794, h6800, h6801, h6802, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6835 | h6835
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6836 | h6836
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6837 | h6837
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6838 | h6838
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6839 | h6839
                          · linarith only [h0, h6794, h6839, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6841 | h6841
                            · linarith only [h0, h6795, h6801, h6841, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6843 | h6843
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6844 | h6844
                                · linarith only [h6835, h6839, h6844, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6846 | h6846
                                  · linarith only [h0, h6795, h6801, h6836, h6846, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6848 | h6848
                                    · linarith only [h6795, h6797, h6801, h6843, h6848, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h1bigk with h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c | h6850c
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h0, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h0, h6835, h6843, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        rcases p6850_3 (m.d 0 1) (by simp) with h6854 | h6854
                                        · rcases p6850_3 (m.d 1 2) (by simp) with h6855 | h6855
                                          · rcases p6850_3 (m.d 1 3) (by simp) with h6856 | h6856
                                            · linarith only [h6794, h6856, hlam]
                                            · linarith only [h6838, h6856, hlam]
                                          · linarith only [h6836, h6855, hlam]
                                        · linarith only [h6854, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p6850_1, u5ehi1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6794, h6835, h6843, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        rcases p6850_3 (m.d 0 1) (by simp) with h6864 | h6864
                                        · linarith only [h0, h6864, hlam]
                                        · linarith only [h6794, h6864, hlam]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        rcases p6850_3 (m.d 0 1) (by simp) with h6867 | h6867
                                        · linarith only [h0, h6867, hlam]
                                        · linarith only [h6795, h6867, hlam]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        rcases p6850_3 (m.d 0 1) (by simp) with h6870 | h6870
                                        · linarith only [h0, h6870, hlam]
                                        · linarith only [h6796, h6870, hlam]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6794, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6835, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6839, h6848, hc14, hc45, hlam, hphi, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6839, hlam, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6795, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6836, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6838, hlam, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6841, hlam, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6796, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h6837, hlam, p6850_0]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h0, h6796, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [h0, h6796, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6850_1]
                                      · have p6850_0 := h6850c.1
                                        have p6850_1 := h6850c.2.1
                                        have p6850_2 := h6850c.2.2.1
                                        have p6850_3 := h6850c.2.2.2
                                        linarith only [hlam, p6850_0]
                              · linarith only [h0, h6794, h6838, h6843, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6889 | h6889
                          · linarith only [h0, h6794, h6889, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6891 | h6891
                            · linarith only [h0, h6794, h6800, h6801, h6838, h6891, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6893 | h6893
                              · linarith only [h6835, h6838, h6893, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6895 | h6895
                                · linarith only [h6800, h6801, h6835, h6837, h6838, h6889, h6895, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6897 | h6897
                                  · linarith only [h6798, h6801, h6897, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6899 | h6899
                                    · linarith only [h6800, h6801, h6899, hlam]
                                    · rcases h1bigk with h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c | h6901c
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        rcases p6901_3 (m.d 0 1) (by simp) with h6904 | h6904
                                        · rcases p6901_3 (m.d 1 2) (by simp) with h6905 | h6905
                                          · rcases p6901_3 (m.d 1 3) (by simp) with h6906 | h6906
                                            · linarith only [h6906, hlam, p6901_0]
                                            · rcases p6901_3 (m.d 1 4) (by simp) with h6908 | h6908
                                              · linarith only [h6795, h6908, hlam]
                                              · linarith only [h6838, h6908, hlam]
                                          · linarith only [h6835, h6905, hlam]
                                        · linarith only [h6904, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        rcases p6901_3 (m.d 0 1) (by simp) with h6913 | h6913
                                        · rcases p6901_3 (m.d 1 2) (by simp) with h6914 | h6914
                                          · rcases p6901_3 (m.d 1 3) (by simp) with h6915 | h6915
                                            · linarith only [h6794, h6915, hlam]
                                            · rcases p6901_3 (m.d 1 4) (by simp) with h6917 | h6917
                                              · linarith only [h6917, hlam, p6901_0]
                                              · rcases p6901_3 (m.d 1 5) (by simp) with h6919 | h6919
                                                · linarith only [h6796, h6919, hlam]
                                                · linarith only [h6891, h6919, hlam]
                                          · linarith only [h6836, h6914, hlam]
                                        · linarith only [h6913, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, h6837, hc12, hlam, hphi, ht01, ht0b, ht5b, p6901_1, u5ehi2]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6794, h6800, h6835, h6838, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, h6794, h6800, h6838, hlam, p6901_2]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        rcases p6901_3 (m.d 0 1) (by simp) with h6928 | h6928
                                        · linarith only [h0, h6928, hlam]
                                        · linarith only [h6795, h6928, hlam]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        rcases p6901_3 (m.d 0 1) (by simp) with h6931 | h6931
                                        · linarith only [h0, h6931, hlam]
                                        · linarith only [h6796, h6931, hlam]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6794, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6835, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6838, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6889, hlam, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6795, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6836, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, h6795, h6835, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6891, hlam, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6796, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h6837, hlam, p6901_0]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, h6796, h6835, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [h0, h6796, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6901_1]
                                      · have p6901_0 := h6901c.1
                                        have p6901_1 := h6901c.2.1
                                        have p6901_2 := h6901c.2.2.1
                                        have p6901_3 := h6901c.2.2.2
                                        linarith only [hlam, p6901_0]
                      · linarith only [h0, h6796, h6837, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h6796, h6836, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h6796, h6835, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h6952 | h6952
                · rcases m.htr 1 2 3 (by decide) (by decide) with h6953 | h6953
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h6954 | h6954
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h6955 | h6955
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h6956 | h6956
                        · linarith only [h0, h6794, h6800, h6956, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h6958 | h6958
                          · linarith only [h0, h6794, h6958, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h6960 | h6960
                            · linarith only [h0, h6795, h6960, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h6962 | h6962
                              · linarith only [h0, h6797, h6800, h6952, h6956, h6960, h6962, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h6964 | h6964
                                · linarith only [h6953, h6958, h6964, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h6966 | h6966
                                  · linarith only [h6954, h6960, h6966, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6968 | h6968
                                    · rcases h1bigk with h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c | h6969c
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        rcases p6969_3 (m.d 0 1) (by simp) with h6972 | h6972
                                        · rcases p6969_3 (m.d 1 2) (by simp) with h6973 | h6973
                                          · rcases p6969_3 (m.d 1 3) (by simp) with h6974 | h6974
                                            · linarith only [h6974, hlam, p6969_0]
                                            · rcases p6969_3 (m.d 1 4) (by simp) with h6976 | h6976
                                              · linarith only [h6795, h6976, hlam]
                                              · linarith only [h6956, h6976, hlam]
                                          · linarith only [h6953, h6973, hlam]
                                        · linarith only [h6972, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        rcases p6969_3 (m.d 0 1) (by simp) with h6981 | h6981
                                        · rcases p6969_3 (m.d 1 2) (by simp) with h6982 | h6982
                                          · rcases p6969_3 (m.d 1 3) (by simp) with h6983 | h6983
                                            · linarith only [h6794, h6983, hlam]
                                            · rcases p6969_3 (m.d 1 4) (by simp) with h6985 | h6985
                                              · linarith only [h6985, hlam, p6969_0]
                                              · rcases p6969_3 (m.d 1 5) (by simp) with h6987 | h6987
                                                · linarith only [h6796, h6987, hlam]
                                                · linarith only [h6960, h6987, hlam]
                                          · linarith only [h6954, h6982, hlam]
                                        · linarith only [h6981, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, h6955, hc12, hlam, hphi, ht01, ht0b, ht5b, p6969_1, u5ehi2]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6795, h6952, h6953, h6956, h6960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, h6795, h6952, h6956, h6960, hlam, p6969_2]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, h6795, h6952, h6960, hlam, p6969_2]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        rcases p6969_3 (m.d 0 1) (by simp) with h6997 | h6997
                                        · linarith only [h0, h6997, hlam]
                                        · linarith only [h6796, h6997, hlam]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6794, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6953, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6956, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6958, hlam, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6795, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6954, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6795, h6952, h6953, h6960, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6960, hlam, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6796, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h6955, hlam, p6969_0]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, h6796, h6953, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [h0, h6795, h6952, h6960, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6969_1]
                                      · have p6969_0 := h6969c.1
                                        have p6969_1 := h6969c.2.1
                                        have p6969_2 := h6969c.2.2.1
                                        have p6969_3 := h6969c.2.2.2
                                        linarith only [hlam, p6969_0]
                                    · linarith only [h6800, h6952, h6968, hlam]
                      · linarith only [h0, h6795, h6952, h6955, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · linarith only [h0, h6795, h6952, h6954, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h6795, h6952, h6953, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7019 | h7019
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7020 | h7020
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7021 | h7021
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7022 | h7022
                        · linarith only [h6794, h6800, h7022, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7024 | h7024
                          · linarith only [h0, h6794, h7024, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7026 | h7026
                            · linarith only [h0, h6795, h6800, h6952, h7026, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7028 | h7028
                              · linarith only [h6794, h6800, h7019, h7028, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7030 | h7030
                                · linarith only [h7019, h7024, h7030, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7032 | h7032
                                  · linarith only [h6795, h6952, h7020, h7032, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7034 | h7034
                                    · rcases h1bigk with h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c | h7035c
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h0, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        rcases p7035_3 (m.d 0 1) (by simp) with h7038 | h7038
                                        · rcases p7035_3 (m.d 1 2) (by simp) with h7039 | h7039
                                          · rcases p7035_3 (m.d 1 3) (by simp) with h7040 | h7040
                                            · linarith only [h7040, hlam, p7035_0]
                                            · rcases p7035_3 (m.d 1 4) (by simp) with h7042 | h7042
                                              · linarith only [h6795, h7042, hlam]
                                              · linarith only [h7022, h7042, hlam]
                                          · linarith only [h7019, h7039, hlam]
                                        · linarith only [h7038, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        rcases p7035_3 (m.d 0 1) (by simp) with h7047 | h7047
                                        · rcases p7035_3 (m.d 1 2) (by simp) with h7048 | h7048
                                          · rcases p7035_3 (m.d 1 3) (by simp) with h7049 | h7049
                                            · linarith only [h6794, h7049, hlam]
                                            · rcases p7035_3 (m.d 1 4) (by simp) with h7051 | h7051
                                              · linarith only [h7051, hlam, p7035_0]
                                              · rcases p7035_3 (m.d 1 5) (by simp) with h7053 | h7053
                                                · linarith only [h6796, h7053, hlam]
                                                · linarith only [h7026, h7053, hlam]
                                          · linarith only [h7020, h7048, hlam]
                                        · linarith only [h7047, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h0, h7021, hc12, hlam, hphi, ht01, ht0b, ht5b, p7035_1, u5ehi2]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h6796, h7021, hc12, hlam, hphi, ht01, ht0b, ht5b, p7035_1, u5ehi2]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        rcases p7035_3 (m.d 0 1) (by simp) with h7061 | h7061
                                        · linarith only [h0, h7061, hlam]
                                        · linarith only [h6794, h7061, hlam]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        rcases p7035_3 (m.d 0 1) (by simp) with h7064 | h7064
                                        · linarith only [h0, h7064, hlam]
                                        · linarith only [h6795, h7064, hlam]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        rcases p7035_3 (m.d 0 1) (by simp) with h7067 | h7067
                                        · linarith only [h0, h7067, hlam]
                                        · linarith only [h6796, h7067, hlam]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h6794, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7019, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7022, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7024, hlam, p7035_1]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h6795, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7020, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h0, h6795, h7019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7035_1]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7026, hlam, p7035_1]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h6796, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h7021, hlam, p7035_0]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h0, h6796, h7019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7035_1]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [h0, h6796, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7035_1]
                                      · have p7035_0 := h7035c.1
                                        have p7035_1 := h7035c.2.1
                                        have p7035_2 := h7035c.2.2.1
                                        have p7035_3 := h7035c.2.2.2
                                        linarith only [hlam, p7035_0]
                                    · rcases h1bigk with h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c | h7085c
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h0, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        rcases p7085_3 (m.d 0 1) (by simp) with h7088 | h7088
                                        · rcases p7085_3 (m.d 1 2) (by simp) with h7089 | h7089
                                          · rcases p7085_3 (m.d 1 3) (by simp) with h7090 | h7090
                                            · linarith only [h7090, hlam, p7085_0]
                                            · rcases p7085_3 (m.d 1 4) (by simp) with h7092 | h7092
                                              · linarith only [h6795, h7092, hlam]
                                              · linarith only [h7022, h7092, hlam]
                                          · linarith only [h7019, h7089, hlam]
                                        · linarith only [h7088, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        rcases p7085_3 (m.d 0 1) (by simp) with h7097 | h7097
                                        · rcases p7085_3 (m.d 1 2) (by simp) with h7098 | h7098
                                          · rcases p7085_3 (m.d 1 3) (by simp) with h7099 | h7099
                                            · linarith only [h6794, h7099, hlam]
                                            · rcases p7085_3 (m.d 1 4) (by simp) with h7101 | h7101
                                              · linarith only [h7101, hlam, p7085_0]
                                              · rcases p7085_3 (m.d 1 5) (by simp) with h7103 | h7103
                                                · linarith only [h6796, h7103, hlam]
                                                · linarith only [h7026, h7103, hlam]
                                          · linarith only [h7020, h7098, hlam]
                                        · linarith only [h7097, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p7085_1, u5ehi1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h6796, hc12, hlam, hphi, ht01, ht0b, ht5b, p7085_1, u5ehi1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        rcases p7085_3 (m.d 0 1) (by simp) with h7111 | h7111
                                        · linarith only [h0, h7111, hlam]
                                        · linarith only [h6794, h7111, hlam]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        rcases p7085_3 (m.d 0 1) (by simp) with h7114 | h7114
                                        · linarith only [h0, h7114, hlam]
                                        · linarith only [h6795, h7114, hlam]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        rcases p7085_3 (m.d 0 1) (by simp) with h7117 | h7117
                                        · linarith only [h0, h7117, hlam]
                                        · linarith only [h6796, h7117, hlam]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h6794, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7019, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7022, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7024, hlam, p7085_1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h6795, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7020, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h0, h6795, h7019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7085_1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7026, hlam, p7085_1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h6796, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h7021, hlam, p7085_0]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h0, h6796, h7019, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7085_1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [h0, h6796, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7085_1]
                                      · have p7085_0 := h7085c.1
                                        have p7085_1 := h7085c.2.1
                                        have p7085_2 := h7085c.2.2.1
                                        have p7085_3 := h7085c.2.2.2
                                        linarith only [hlam, p7085_0]
                      · linarith only [h0, h6796, h7021, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h6796, h7020, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h6796, h7019, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h0, h6796, h6799, hlam]
          · linarith only [h0, h6795, h6798, hlam]
        · linarith only [h0, h6794, h6797, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7141 | h7141
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7142 | h7142
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7143 | h7143
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7144 | h7144
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7145 | h7145
                · linarith only [h6794, h6796, h7144, h7145, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7147 | h7147
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7148 | h7148
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7149 | h7149
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7150 | h7150
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7151 | h7151
                          · linarith only [h6794, h6796, h7149, h7151, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7153 | h7153
                            · linarith only [h6794, h6796, h7150, h7151, h7153, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h6794, h6796, h7150, h7153, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7156 | h7156
                          · linarith only [h6794, h7144, h7150, h7156, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h6794, h6796, h7144, h7150, h7156, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h6794, h7143, h7144, h7149, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7142, h7148, hlam]
                  · linarith only [h0, h7141, h7147, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7162 | h7162
                · linarith only [h6795, h6796, h7162, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7164 | h7164
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7165 | h7165
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7166 | h7166
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7167 | h7167
                        · linarith only [h6794, h6796, h7144, h7166, h7167, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7169 | h7169
                          · linarith only [h6795, h6796, h7166, h7167, h7169, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7171 | h7171
                            · linarith only [h6795, h6796, h7162, h7169, h7171, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7173 | h7173
                              · linarith only [h6794, h7144, h7164, h7173, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7175 | h7175
                                · linarith only [h6795, h6796, h7164, h7167, h7171, h7175, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7177 | h7177
                                  · linarith only [h6795, h6796, h7165, h7171, h7177, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7179 | h7179
                                    · linarith only [h6795, h6796, h7167, h7171, h7179, hc13, hc34, hlam, hphi]
                                    · rcases h1bigk with h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c | h7181c
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h0, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6796, h7164, h7169, hc23, hc35, hlam, hphi, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6796, h7164, h7167, h7169, hc23, hc35, hlam, hphi, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6796, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7187 | h7187
                                        · linarith only [h7187, hlam, p7181_0]
                                        · rcases p7181_3 (m.d 1 2) (by simp) with h7189 | h7189
                                          · rcases p7181_3 (m.d 1 3) (by simp) with h7190 | h7190
                                            · linarith only [h7164, h7190, hlam]
                                            · rcases p7181_3 (m.d 1 4) (by simp) with h7192 | h7192
                                              · linarith only [h7165, h7192, hlam]
                                              · rcases p7181_3 (m.d 1 5) (by simp) with h7194 | h7194
                                                · linarith only [h7166, h7194, hlam]
                                                · linarith only [h6796, h7194, hlam]
                                          · linarith only [h7189, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7199 | h7199
                                        · linarith only [h0, h7199, hlam]
                                        · linarith only [h6794, h7199, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7202 | h7202
                                        · linarith only [h0, h7202, hlam]
                                        · linarith only [h6795, h7202, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6795, h6796, h7164, h7167, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6794, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7164, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7167, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7169, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6795, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7165, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6795, h6796, h7164, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7171, hlam, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h6795, h7169, h7179, hc14, hc45, hlam, hphi, p7181_1]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [h7166, hlam, p7181_0]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7218 | h7218
                                        · linarith only [h6796, h7218, hlam]
                                        · linarith only [h6794, h7218, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        rcases p7181_3 (m.d 0 1) (by simp) with h7221 | h7221
                                        · linarith only [h6796, h7221, hlam]
                                        · linarith only [h6795, h7221, hlam]
                                      · have p7181_0 := h7181c.1
                                        have p7181_1 := h7181c.2.1
                                        have p7181_2 := h7181c.2.2.1
                                        have p7181_3 := h7181c.2.2.2
                                        linarith only [hlam, p7181_0]
                      · linarith only [h0, h6795, h7143, h7166, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7142, h7165, hlam]
                  · linarith only [h0, h7141, h7164, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7228 | h7228
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7229 | h7229
                · linarith only [h6794, h6796, h7228, h7229, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7231 | h7231
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7232 | h7232
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7233 | h7233
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7234 | h7234
                        · linarith only [h0, h6794, h7143, h7233, h7234, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h6794, h7143, h7228, h7233, h7234, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7237 | h7237
                        · linarith only [h0, h6794, h7233, h7237, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h6794, h7228, h7233, h7237, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6794, h7142, h7143, h7228, h7232, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h7141, h7231, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7242 | h7242
                · linarith only [h6795, h6796, h7242, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7244 | h7244
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7245 | h7245
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7246 | h7246
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7247 | h7247
                        · linarith only [h0, h6794, h7228, h7247, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7249 | h7249
                          · linarith only [h0, h6794, h7143, h7246, h7249, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7251 | h7251
                            · linarith only [h0, h6795, h7143, h7246, h7251, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7253 | h7253
                              · linarith only [h7141, h7143, h7228, h7246, h7253, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7255 | h7255
                                · linarith only [h0, h6794, h7143, h7244, h7246, h7255, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7257 | h7257
                                  · linarith only [h0, h6795, h7143, h7245, h7246, h7251, h7257, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7259 | h7259
                                    · linarith only [h0, h6795, h7143, h7246, h7247, h7251, h7259, hc13, hc34, hlam, hphi]
                                    · rcases h1bigk with h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c | h7261c
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h7143, h7244, h7246, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h7143, h7246, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h6796, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        rcases p7261_3 (m.d 0 1) (by simp) with h7267 | h7267
                                        · linarith only [h7267, hlam, p7261_0]
                                        · rcases p7261_3 (m.d 1 2) (by simp) with h7269 | h7269
                                          · rcases p7261_3 (m.d 1 3) (by simp) with h7270 | h7270
                                            · linarith only [h7244, h7270, hlam]
                                            · rcases p7261_3 (m.d 1 4) (by simp) with h7272 | h7272
                                              · linarith only [h7245, h7272, hlam]
                                              · rcases p7261_3 (m.d 1 5) (by simp) with h7274 | h7274
                                                · linarith only [h7246, h7274, hlam]
                                                · linarith only [h6796, h7274, hlam]
                                          · linarith only [h7269, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h6794, h7143, h7246, hlam, p7261_2]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h6795, h7143, h7246, hlam, p7261_2]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h7143, h7246, hc01, hc12, hlam, hphi, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h6794, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7244, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7247, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7249, hlam, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h6795, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7245, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h0, h6795, h7143, h7246, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7251, hlam, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h6794, h7249, hc13, hc35, hlam, hphi, p7261_1]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [h7246, hlam, p7261_0]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        rcases p7261_3 (m.d 0 1) (by simp) with h7294 | h7294
                                        · linarith only [h6796, h7294, hlam]
                                        · linarith only [h6794, h7294, hlam]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        rcases p7261_3 (m.d 0 1) (by simp) with h7297 | h7297
                                        · linarith only [h6796, h7297, hlam]
                                        · linarith only [h6795, h7297, hlam]
                                      · have p7261_0 := h7261c.1
                                        have p7261_1 := h7261c.2.1
                                        have p7261_2 := h7261c.2.2.1
                                        have p7261_3 := h7261c.2.2.2
                                        linarith only [hlam, p7261_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7301 | h7301
                        · linarith only [h0, h6794, h7228, h7246, h7301, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7303 | h7303
                          · linarith only [h0, h6794, h7246, h7303, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7305 | h7305
                            · linarith only [h0, h6795, h7246, h7305, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7307 | h7307
                              · linarith only [h0, h7141, h7228, h7246, h7307, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7309 | h7309
                                · linarith only [h0, h6794, h6796, h7244, h7246, h7303, h7309, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                                · linarith only [h0, h6795, h7244, h7246, h7301, h7309, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h6795, h7142, h7143, h7245, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h6794, h7141, h7244, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h6795, h7142, hlam]
        · linarith only [h0, h6794, h7141, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h7316 | h7316
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7317 | h7317
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7318 | h7318
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7319 | h7319
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7320 | h7320
              · linarith only [h6794, h6795, h7320, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7322 | h7322
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7323 | h7323
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7324 | h7324
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7325 | h7325
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7326 | h7326
                        · linarith only [h6794, h6795, h7320, h7326, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7328 | h7328
                          · linarith only [h6794, h6795, h7326, h7328, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7330 | h7330
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7331 | h7331
                              · linarith only [h6795, h7316, h7323, h7326, h7328, h7331, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7333 | h7333
                                · linarith only [h7323, h7328, h7333, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7335 | h7335
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7336 | h7336
                                    · rcases h1bigk with h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c | h7337c
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h0, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h6795, h7326, hc13, hc34, hlam, hphi, p7337_1]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h6795, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h6795, h7326, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7337_1, u5ehi1]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7316, hc12, hlam, hphi, ht01, ht0b, ht5b, p7337_1, u5ehi1]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        rcases p7337_3 (m.d 0 1) (by simp) with h7345 | h7345
                                        · linarith only [h0, h7345, hlam]
                                        · linarith only [h6794, h7345, hlam]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h6795, h7316, h7325, h7335, hc12, hlam, hphi, ht01, ht0b, ht5b, p7337_1, u5ehi4]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        rcases p7337_3 (m.d 0 1) (by simp) with h7349 | h7349
                                        · linarith only [h0, h7349, hlam]
                                        · linarith only [h7316, h7349, hlam]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h6794, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7323, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7326, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7328, hlam, p7337_1]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7316, h7325, h7335, hc14, hlam, hphi, ht01, ht0b, ht5b, p7337_1, u5ehi4]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7324, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        rcases p7337_3 (m.d 0 1) (by simp) with h7359 | h7359
                                        · linarith only [h6795, h7359, hlam]
                                        · linarith only [h6794, h7359, hlam]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        rcases p7337_3 (m.d 0 1) (by simp) with h7363 | h7363
                                        · linarith only [h6795, h7363, hlam]
                                        · linarith only [h7316, h7363, hlam]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7316, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7325, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h0, h7316, h7323, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7337_1]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [h7330, hlam, p7337_0]
                                      · have p7337_0 := h7337c.1
                                        have p7337_1 := h7337c.2.1
                                        have p7337_2 := h7337c.2.2.1
                                        have p7337_3 := h7337c.2.2.2
                                        linarith only [hlam, p7337_0]
                                    · linarith only [h6795, h7316, h7325, h7326, h7335, h7336, hlam]
                                  · linarith only [h6795, h7316, h7326, h7330, h7331, h7335, hc23, hc34, hlam, hphi]
                            · linarith only [h6795, h7316, h7330, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
                      · linarith only [h6795, h7316, h7324, h7325, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h7316, h7324, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h7316, h7323, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h6795, h7316, h7322, hlam]
            · linarith only [h6795, h7316, h7318, h7319, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7379 | h7379
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7380 | h7380
              · linarith only [h0, h6794, h7318, h7380, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7382 | h7382
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7383 | h7383
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7384 | h7384
                    · linarith only [h7318, h7379, h7384, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · linarith only [h0, h7316, h7384, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h7316, h7383, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h7316, h7318, h7382, hlam]
            · linarith only [h0, h7316, h7379, hlam]
        · linarith only [h0, h6794, h7317, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h7391 | h7391
        · rcases m.htr 0 2 4 (by decide) (by decide) with h7392 | h7392
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7393 | h7393
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7394 | h7394
              · linarith only [h6794, h6795, h7394, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7396 | h7396
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7397 | h7397
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7398 | h7398
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7399 | h7399
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7400 | h7400
                        · linarith only [h6794, h6795, h7394, h7398, h7400, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7402 | h7402
                          · linarith only [h6794, h6795, h7400, h7402, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7404 | h7404
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7405 | h7405
                              · linarith only [h6794, h7316, h7391, h7400, h7404, h7405, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7407 | h7407
                                · linarith only [h6794, h7316, h7397, h7402, h7407, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7409 | h7409
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7410 | h7410
                                    · rcases h1bigk with h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c | h7411c
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h0, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7316, h7397, h7400, h7404, hc23, hc34, hlam, hphi, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6795, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7316, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        rcases p7411_3 (m.d 0 1) (by simp) with h7417 | h7417
                                        · linarith only [h7417, hlam, p7411_0]
                                        · rcases p7411_3 (m.d 1 2) (by simp) with h7419 | h7419
                                          · rcases p7411_3 (m.d 1 3) (by simp) with h7420 | h7420
                                            · linarith only [h7397, h7420, hlam]
                                            · rcases p7411_3 (m.d 1 4) (by simp) with h7422 | h7422
                                              · linarith only [h7398, h7422, hlam]
                                              · linarith only [h6795, h7422, hlam]
                                          · linarith only [h7419, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        rcases p7411_3 (m.d 0 1) (by simp) with h7427 | h7427
                                        · linarith only [h0, h7427, hlam]
                                        · linarith only [h6794, h7427, hlam]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6795, hc01, hc12, hlam, hphi, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6794, h7316, h7397, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6794, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7397, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7400, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7402, hlam, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6794, h7397, h7400, hc23, hc34, hlam, hphi, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7398, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        rcases p7411_3 (m.d 0 1) (by simp) with h7439 | h7439
                                        · linarith only [h6795, h7439, hlam]
                                        · linarith only [h6794, h7439, hlam]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6794, h7316, h7397, h7400, hc23, hc34, hlam, hphi, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h6794, h7397, h7402, hc23, hc35, hlam, hphi, p7411_1]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7399, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        rcases p7411_3 (m.d 0 1) (by simp) with h7446 | h7446
                                        · linarith only [h7316, h7446, hlam]
                                        · linarith only [h6794, h7446, hlam]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [h7404, hlam, p7411_0]
                                      · have p7411_0 := h7411c.1
                                        have p7411_1 := h7411c.2.1
                                        have p7411_2 := h7411c.2.2.1
                                        have p7411_3 := h7411c.2.2.2
                                        linarith only [hlam, p7411_0]
                                    · linarith only [h6794, h6795, h7392, h7397, h7400, h7409, h7410, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7452 | h7452
                                    · rcases h1bigk with h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c | h7453c
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h0, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6795, h7397, h7400, hc23, hc34, hlam, hphi, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6795, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7316, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        rcases p7453_3 (m.d 0 1) (by simp) with h7459 | h7459
                                        · linarith only [h7459, hlam, p7453_0]
                                        · rcases p7453_3 (m.d 1 2) (by simp) with h7461 | h7461
                                          · rcases p7453_3 (m.d 1 3) (by simp) with h7462 | h7462
                                            · linarith only [h7397, h7462, hlam]
                                            · rcases p7453_3 (m.d 1 4) (by simp) with h7464 | h7464
                                              · linarith only [h7398, h7464, hlam]
                                              · linarith only [h6795, h7464, hlam]
                                          · linarith only [h7461, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        rcases p7453_3 (m.d 0 1) (by simp) with h7469 | h7469
                                        · linarith only [h0, h7469, hlam]
                                        · linarith only [h6794, h7469, hlam]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6795, h7396, h7409, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7316, hc01, hc12, hlam, hphi, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6794, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7397, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7400, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7402, hlam, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6794, h7397, h7400, hc23, hc34, hlam, hphi, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7398, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        rcases p7453_3 (m.d 0 1) (by simp) with h7481 | h7481
                                        · linarith only [h6795, h7481, hlam]
                                        · linarith only [h6794, h7481, hlam]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6794, h7316, h7397, h7400, hc23, hc34, hlam, hphi, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h6794, h7397, h7402, hc23, hc35, hlam, hphi, p7453_1]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7399, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        rcases p7453_3 (m.d 0 1) (by simp) with h7488 | h7488
                                        · linarith only [h7316, h7488, hlam]
                                        · linarith only [h6794, h7488, hlam]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [h7404, hlam, p7453_0]
                                      · have p7453_0 := h7453c.1
                                        have p7453_1 := h7453c.2.1
                                        have p7453_2 := h7453c.2.2.1
                                        have p7453_3 := h7453c.2.2.2
                                        linarith only [hlam, p7453_0]
                                    · linarith only [h6794, h6795, h7396, h7400, h7452, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h6794, h6795, h7397, h7404, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h7392, h7393, h7396, h7399, hlam]
                    · linarith only [h0, h7392, h7398, hlam]
                  · linarith only [h0, h7391, h7397, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7498 | h7498
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7499 | h7499
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7500 | h7500
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7501 | h7501
                        · linarith only [h6794, h6795, h7394, h7499, h7501, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7503 | h7503
                          · linarith only [h6794, h6795, h7396, h7503, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7505 | h7505
                            · linarith only [h6794, h6795, h7396, h7501, h7505, hc13, hc34, hlam, hphi]
                            · linarith only [h6794, h6795, h7498, h7505, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6794, h7393, h7498, h7500, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7392, h7499, hlam]
                  · linarith only [h0, h6794, h7391, h7498, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7511 | h7511
              · linarith only [h6794, h6795, h7511, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7513 | h7513
                · linarith only [h7392, h7393, h7513, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7515 | h7515
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7516 | h7516
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7517 | h7517
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7518 | h7518
                        · linarith only [h6794, h6795, h7511, h7518, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7520 | h7520
                          · linarith only [h6794, h6795, h7392, h7393, h7517, h7520, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7522 | h7522
                            · linarith only [h6794, h6795, h7513, h7518, h7522, hc13, hc34, hlam, hphi]
                            · linarith only [h6794, h6795, h7515, h7522, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7525 | h7525
                        · linarith only [h0, h6794, h7517, h7525, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7527 | h7527
                          · linarith only [h6794, h6795, h7516, h7517, h7527, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7529 | h7529
                            · linarith only [h6794, h6795, h7513, h7515, h7516, h7517, h7529, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h6794, h6795, h7515, h7529, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7392, h7516, hlam]
                  · linarith only [h0, h6794, h7391, h7515, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h7534 | h7534
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7535 | h7535
              · linarith only [h0, h6794, h7392, h7535, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7537 | h7537
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7538 | h7538
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7539 | h7539
                    · linarith only [h7392, h7534, h7539, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7541 | h7541
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7542 | h7542
                        · linarith only [h6794, h7316, h7535, h7542, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7544 | h7544
                          · linarith only [h6794, h7316, h7539, h7541, h7544, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7546 | h7546
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7547 | h7547
                              · linarith only [h6794, h7316, h7391, h7392, h7539, h7541, h7542, h7547, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h6794, h7316, h7538, h7539, h7541, h7547, hc23, hc34, hlam, hphi]
                            · linarith only [h6794, h7316, h7538, h7539, h7541, h7546, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h7534, h7541, hlam]
                  · linarith only [h0, h7391, h7538, hlam]
                · linarith only [h7392, h7534, h7537, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h7554 | h7554
              · linarith only [h0, h6794, h7392, h7554, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7556 | h7556
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7557 | h7557
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7558 | h7558
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7559 | h7559
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7560 | h7560
                        · linarith only [h0, h6794, h7392, h7554, h7558, h7560, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7562 | h7562
                          · linarith only [h0, h6794, h7392, h7558, h7562, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7564 | h7564
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7565 | h7565
                              · linarith only [h7391, h7534, h7559, h7560, h7564, h7565, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7567 | h7567
                                · linarith only [h0, h6794, h7534, h7557, h7559, h7562, h7567, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7569 | h7569
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7570 | h7570
                                    · rcases h1bigk with h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c | h7571c
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, h7534, h7558, h7569, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h6795, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7316, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        rcases p7571_3 (m.d 0 1) (by simp) with h7577 | h7577
                                        · linarith only [h7577, hlam, p7571_0]
                                        · rcases p7571_3 (m.d 1 2) (by simp) with h7579 | h7579
                                          · rcases p7571_3 (m.d 1 3) (by simp) with h7580 | h7580
                                            · linarith only [h7557, h7580, hlam]
                                            · rcases p7571_3 (m.d 1 4) (by simp) with h7582 | h7582
                                              · linarith only [h7558, h7582, hlam]
                                              · linarith only [h6795, h7582, hlam]
                                          · linarith only [h7579, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, h6794, h7534, h7558, h7569, hlam, p7571_2]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, h7534, h7559, h7564, hc01, hc12, hlam, hphi, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, h6794, h7534, h7557, h7559, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h6794, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7557, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7560, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7562, hlam, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h6794, h7557, h7560, hc23, hc34, hlam, hphi, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7558, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        rcases p7571_3 (m.d 0 1) (by simp) with h7597 | h7597
                                        · linarith only [h6795, h7597, hlam]
                                        · linarith only [h6794, h7597, hlam]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h0, h6794, h7534, h7557, h7559, h7560, hc23, hc34, hlam, hphi, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h6794, h7557, h7562, hc23, hc35, hlam, hphi, p7571_1]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7559, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        rcases p7571_3 (m.d 0 1) (by simp) with h7604 | h7604
                                        · linarith only [h7316, h7604, hlam]
                                        · linarith only [h6794, h7604, hlam]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [h7564, hlam, p7571_0]
                                      · have p7571_0 := h7571c.1
                                        have p7571_1 := h7571c.2.1
                                        have p7571_2 := h7571c.2.2.1
                                        have p7571_3 := h7571c.2.2.2
                                        linarith only [hlam, p7571_0]
                                    · linarith only [h6794, h6795, h7556, h7557, h7560, h7570, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h7392, h7556, h7569, hlam]
                            · linarith only [h6794, h6795, h7556, h7557, h7564, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h6794, h7392, h7557, h7558, h7559, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7613 | h7613
                      · linarith only [h0, h6794, h7534, h7557, h7558, h7613, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7615 | h7615
                        · linarith only [h0, h6794, h7554, h7556, h7615, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7617 | h7617
                          · linarith only [h0, h6794, h7558, h7617, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7619 | h7619
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7620 | h7620
                              · linarith only [h0, h6794, h6795, h7557, h7558, h7615, h7620, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h6794, h7557, h7558, h7620, hc23, hc34, hlam, hphi]
                            · linarith only [h6794, h6795, h7556, h7557, h7619, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h7391, h7557, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7625 | h7625
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7626 | h7626
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7627 | h7627
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7628 | h7628
                        · linarith only [h0, h6794, h7392, h7626, h7628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7630 | h7630
                          · linarith only [h0, h6794, h7392, h7626, h7630, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7632 | h7632
                            · linarith only [h0, h6794, h7392, h7556, h7628, h7632, hc13, hc34, hlam, hphi]
                            · linarith only [h6794, h6795, h7625, h7632, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h0, h6794, h7392, h7625, h7626, h7627, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7636 | h7636
                      · linarith only [h0, h6794, h7534, h7625, h7626, h7636, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7638 | h7638
                        · linarith only [h0, h6794, h7626, h7638, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7640 | h7640
                          · linarith only [h0, h6794, h7626, h7640, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7642 | h7642
                            · linarith only [h0, h6794, h7392, h7556, h7625, h7638, h7642, hc23, hc34, hlam, hphi]
                            · linarith only [h6794, h6795, h7625, h7642, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h6794, h7391, h7625, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h0, h6794, h7391, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s8 m hb1 hb2 hb4 hb5 h0 h6794

set_option maxHeartbeats 24852000 in
set_option maxHeartbeats 24852000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_IR_s7 m hb1 hb2 hb4 hb5 h0

end R2N4
