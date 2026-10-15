import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_64S5

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_I_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h802 | h802
  · rcases m.htr 0 2 3 (by decide) (by decide) with h803 | h803
    · rcases m.htr 0 2 4 (by decide) (by decide) with h804 | h804
      · rcases m.htr 0 3 4 (by decide) (by decide) with h805 | h805
        · rcases m.htr 0 4 5 (by decide) (by decide) with h806 | h806
          · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
            · rcases m.htr 1 2 4 (by decide) (by decide) with h808 | h808
              · rcases m.htr 1 3 4 (by decide) (by decide) with h809 | h809
                · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h811 | h811
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h812 | h812
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h813 | h813
                        · linarith only [h803, h811, h813, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h0, h802, h810, h813, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h802, h810, h812, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h817 | h817
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h818 | h818
                        · rcases h4bigk with h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c | h819c
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h808, h817, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h817, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            rcases p819_3 (m.d 0 4) (by simp) with h824 | h824
                            · rcases p819_3 (m.d 1 4) (by simp) with h825 | h825
                              · linarith only [h802, h825, hlam]
                              · linarith only [h810, h825, hlam]
                            · linarith only [h824, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h802, hlam, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h817, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h804, hlam, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h808, hlam, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h811, hlam, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h804, hc45, hlam, hphi, ht0b, ht5b, p819_1, u0elo1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h805, hlam, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h809, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h805, hc24, hlam, hphi, ht0b, ht45, ht5b, p819_1, u0elo2]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h0, h802, h809, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p819_1]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h806, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h810, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h817, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [h818, hlam, p819_0]
                          · have p819_0 := h819c.1
                            have p819_1 := h819c.2.1
                            have p819_2 := h819c.2.2.1
                            have p819_3 := h819c.2.2.2
                            linarith only [hlam, p819_0]
                        · linarith only [h804, h817, h818, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h802, h810, h817, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h851 | h851
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h852 | h852
                      · linarith only [h808, h810, h852, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h854 | h854
                        · linarith only [h808, h810, h851, h854, hlam]
                        · rcases h4bigk with h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c | h856c
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h858 | h858
                            · rcases p856_3 (m.d 1 4) (by simp) with h859 | h859
                              · linarith only [h802, h859, hlam]
                              · rcases p856_3 (m.d 2 4) (by simp) with h861 | h861
                                · linarith only [h804, h861, hlam]
                                · rcases p856_3 (m.d 3 4) (by simp) with h863 | h863
                                  · linarith only [h805, h863, hlam]
                                  · rcases p856_3 (m.d 4 5) (by simp) with h865 | h865
                                    · linarith only [h806, h865, hlam]
                                    · linarith only [h810, h865, hlam]
                            · linarith only [h802, h858, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h869 | h869
                            · rcases p856_3 (m.d 1 4) (by simp) with h870 | h870
                              · linarith only [h802, h870, hlam]
                              · linarith only [h808, h870, hlam]
                            · linarith only [h804, h869, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            rcases p856_3 (m.d 0 4) (by simp) with h874 | h874
                            · rcases p856_3 (m.d 1 4) (by simp) with h875 | h875
                              · linarith only [h802, h875, hlam]
                              · linarith only [h809, h875, hlam]
                            · linarith only [h805, h874, hlam]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h802, h810, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h802, hlam, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h810, h851, hc34, hc45, hlam, hphi, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h802, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h810, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h804, hlam, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h808, hlam, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h804, hc34, hlam, hphi, ht0b, ht45, ht5b, p856_1, u0elo1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h852, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h805, hlam, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h809, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h851, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h854, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h806, hlam, p856_0]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h802, h806, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h802, h806, h851, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [h0, h802, h806, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p856_1]
                          · have p856_0 := h856c.1
                            have p856_1 := h856c.2.1
                            have p856_2 := h856c.2.2.1
                            have p856_3 := h856c.2.2.2
                            linarith only [hlam, p856_0]
                    · linarith only [h0, h802, h806, h809, h810, h851, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
                    · linarith only [h807, h809, h902, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h904 | h904
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h905 | h905
                        · rcases h4bigk with h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c | h906c
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h0, h802, h808, h904, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h0, h802, h904, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h0, h802, h807, h809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            rcases p906_3 (m.d 0 4) (by simp) with h911 | h911
                            · rcases p906_3 (m.d 1 4) (by simp) with h912 | h912
                              · linarith only [h802, h912, hlam]
                              · linarith only [h901, h912, hlam]
                            · linarith only [h911, hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h802, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h0, h802, h904, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h809, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h803, h805, h809, hc45, hlam, hphi, ht0b, ht5b, p906_1, u0elo1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h804, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h808, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h902, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h804, hc45, hlam, hphi, ht0b, ht5b, p906_1, u0elo1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h805, hlam, p906_1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h803, h805, hc14, hlam, hphi, ht0b, ht45, ht5b, p906_1, u0elo1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h803, h805, hc24, hlam, hphi, ht0b, ht45, ht5b, p906_1, u0elo1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h803, h805, hc45, hlam, hphi, ht0b, ht5b, p906_1, u0elo1]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h806, hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h901, hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h904, hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [h905, hlam, p906_0]
                          · have p906_0 := h906c.1
                            have p906_1 := h906c.2.1
                            have p906_2 := h906c.2.2.1
                            have p906_3 := h906c.2.2.2
                            linarith only [hlam, p906_0]
                        · linarith only [h804, h809, h904, h905, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h0, h802, h901, h904, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                    · linarith only [h807, h809, h938, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h940 | h940
                      · linarith only [h804, h809, h901, h940, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                        · linarith only [h803, h805, h807, h809, h901, h942, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h802, h806, h807, h809, h942, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h808, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h802, h806, h807, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
            · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
              · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
                · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                  · linarith only [h806, h950, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h952 | h952
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h953 | h953
                      · linarith only [h0, h802, h806, h948, h953, hc12, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h955 | h955
                        · linarith only [h803, h806, h952, h955, hlam, hphi, u0ehi8, u0elo1]
                        · rcases h4bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h806, h948, hc24, hc45, hlam, hphi, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h806, hc24, hc45, hlam, hphi, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h806, hc34, hc45, hlam, hphi, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h806, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h802, hlam, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h0, h802, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h0, h802, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h950, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h804, hlam, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h948, hlam, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h804, hc34, hlam, hphi, ht0b, ht45, ht5b, p957_1, u0elo1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h953, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h805, hlam, p957_1]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h949, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h952, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [h955, hlam, p957_0]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p957_1, u0ehi8]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            rcases p957_3 (m.d 0 4) (by simp) with h979 | h979
                            · linarith only [h806, h979, hlam]
                            · linarith only [h802, h979, hlam]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            rcases p957_3 (m.d 0 4) (by simp) with h982 | h982
                            · linarith only [h806, h982, hlam]
                            · linarith only [h804, h982, hlam]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            rcases p957_3 (m.d 0 4) (by simp) with h985 | h985
                            · linarith only [h806, h985, hlam]
                            · linarith only [h805, h985, hlam]
                          · have p957_0 := h957c.1
                            have p957_1 := h957c.2.1
                            have p957_2 := h957c.2.2.1
                            have p957_3 := h957c.2.2.2
                            linarith only [hlam, p957_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h989 | h989
                      · linarith only [h806, h949, h952, h989, hc13, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h991 | h991
                        · linarith only [h0, h802, h806, h949, h991, hc12, hlam, hphi, ht01, u0ehi8]
                        · rcases h4bigk with h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h806, hc14, hc45, hlam, hphi, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h806, hc24, hc45, hlam, hphi, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h806, h952, hc24, hc45, hlam, hphi, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h806, hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h802, hlam, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h802, hc24, hlam, hphi, ht0b, ht45, ht5b, p993_1, u0elo0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h0, h802, h952, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h950, hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h804, hlam, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h948, hlam, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h952, hlam, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h989, hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h805, hlam, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h949, hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h803, h805, hc24, hlam, hphi, ht0b, ht45, ht5b, p993_1, u0elo1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h991, hlam, p993_0]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p993_1, u0ehi8]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h949, h952, hc23, hc45, hlam, hphi, ht34, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            rcases p993_3 (m.d 0 4) (by simp) with h1016 | h1016
                            · linarith only [h1016, h806, hlam]
                            · linarith only [h1016, h804, hlam]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [h952, hc23, hc45, hlam, hphi, ht34, p993_1]
                          · have p993_0 := h993c.1
                            have p993_1 := h993c.2.1
                            have p993_2 := h993c.2.2.1
                            have p993_3 := h993c.2.2.2
                            linarith only [hlam, p993_0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1021 | h1021
                  · linarith only [h1021, h803, h805, h806, h949, hlam, hphi, u0ehi8, u0elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1023 | h1023
                    · linarith only [h1023, h947, h949, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1025 | h1025
                      · linarith only [h1025, h806, h948, hc14, hlam, hphi, ht01, u0ehi8]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1027 | h1027
                        · linarith only [h1027, h803, h805, h806, hlam, hphi, u0ehi8, u0elo1]
                        · rcases h4bigk with h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c | h1029c
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h806, h948, hc24, hc45, hlam, hphi, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h806, hc24, hc45, hlam, hphi, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h806, hc34, hc45, hlam, hphi, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h806, hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h802, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h0, h802, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h949, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h1021, hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h804, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h948, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h1023, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h1025, hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h805, hlam, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h803, h805, hc14, hlam, hphi, ht0b, ht45, ht5b, p1029_1, u0elo1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h803, h805, hc24, hlam, hphi, ht0b, ht45, ht5b, p1029_1, u0elo1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h1027, hlam, p1029_0]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p1029_1, u0ehi8]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            rcases p1029_3 (m.d 0 4) (by simp) with h1051 | h1051
                            · linarith only [h1051, h806, hlam]
                            · linarith only [h1051, h802, hlam]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            rcases p1029_3 (m.d 0 4) (by simp) with h1054 | h1054
                            · linarith only [h1054, h806, hlam]
                            · linarith only [h1054, h804, hlam]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [h947, h949, hc23, hc45, hlam, hphi, ht34, p1029_1]
                          · have p1029_0 := h1029c.1
                            have p1029_1 := h1029c.2.1
                            have p1029_2 := h1029c.2.2.1
                            have p1029_3 := h1029c.2.2.2
                            linarith only [hlam, p1029_0]
              · linarith only [h0, h948, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h802, h947, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1061 | h1061
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1062 | h1062
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1063 | h1063
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
                · linarith only [h1064, h805, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1066 | h1066
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1067 | h1067
                    · linarith only [h1062, h1067, h805, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1069 | h1069
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1070 | h1070
                        · rcases h4bigk with h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h0, h1066, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h0, h1069, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h805, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            rcases p1071_3 (m.d 0 4) (by simp) with h1076 | h1076
                            · rcases p1071_3 (m.d 1 4) (by simp) with h1077 | h1077
                              · linarith only [h1077, h802, hlam]
                              · linarith only [h1066, h1077, hlam]
                            · linarith only [h1076, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h802, hlam, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h0, h1069, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1064, hlam, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h0, h802, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h804, hlam, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1063, hlam, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1067, hlam, p1071_1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h804, hc45, hlam, hphi, ht0b, ht5b, p1071_1, u0elo1]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1071_1, u0ehi8]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            rcases p1071_3 (m.d 0 4) (by simp) with h1092 | h1092
                            · linarith only [h1092, h805, hlam]
                            · linarith only [h1092, h802, hlam]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            rcases p1071_3 (m.d 0 4) (by simp) with h1095 | h1095
                            · linarith only [h1095, h805, hlam]
                            · linarith only [h1095, h804, hlam]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            rcases p1071_3 (m.d 0 4) (by simp) with h1099 | h1099
                            · linarith only [h1099, h805, hlam]
                            · linarith only [h1061, h1099, hlam]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1061, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1066, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1069, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [h1070, hlam, p1071_0]
                          · have p1071_0 := h1071c.1
                            have p1071_1 := h1071c.2.1
                            have p1071_2 := h1071c.2.2.1
                            have p1071_3 := h1071c.2.2.2
                            linarith only [hlam, p1071_0]
                        · linarith only [h0, h1063, h1069, h1070, h802, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1066, h1067, h1069, h802, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                    · linarith only [h1061, h1062, h1064, h1066, h1109, h805, hlam, hphi, u0ehi7, u0elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1111 | h1111
                      · linarith only [h1064, h1066, h1111, h804, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                        · rcases h4bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1116 | h1116
                            · rcases p1114_3 (m.d 1 4) (by simp) with h1117 | h1117
                              · linarith only [h1117, h802, hlam]
                              · rcases p1114_3 (m.d 2 4) (by simp) with h1119 | h1119
                                · linarith only [h1119, h804, hlam]
                                · rcases p1114_3 (m.d 3 4) (by simp) with h1121 | h1121
                                  · rcases p1114_3 (m.d 4 5) (by simp) with h1122 | h1122
                                    · linarith only [h1061, h1122, hlam]
                                    · linarith only [h1066, h1122, hlam]
                                  · linarith only [h1064, h1121, hlam]
                            · linarith only [h1116, h802, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1127 | h1127
                            · rcases p1114_3 (m.d 1 4) (by simp) with h1128 | h1128
                              · linarith only [h1128, h802, hlam]
                              · linarith only [h1063, h1128, hlam]
                            · linarith only [h1127, h804, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h805, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h0, h1062, h1064, h1066, h802, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h802, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1066, hc24, hc45, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1064, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1066, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h804, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1063, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1109, hlam, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1111, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p1114_1, u0ehi8]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1145 | h1145
                            · linarith only [h1145, h805, hlam]
                            · linarith only [h1145, h802, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            rcases p1114_3 (m.d 0 4) (by simp) with h1148 | h1148
                            · linarith only [h1148, h805, hlam]
                            · linarith only [h1148, h804, hlam]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1062, h1064, h1066, hc23, hc34, hlam, hphi, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1061, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h0, h1061, h1062, h1064, h802, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h0, h1061, h1109, h802, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1114_1]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [h1113, hlam, p1114_0]
                          · have p1114_0 := h1114c.1
                            have p1114_1 := h1114c.2.1
                            have p1114_2 := h1114c.2.2.1
                            have p1114_3 := h1114c.2.2.2
                            linarith only [hlam, p1114_0]
                        · linarith only [h0, h1061, h1113, h802, h805, hc12, hlam, hphi, ht01, u0ehi7]
              · linarith only [h0, h1063, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1062, h802, h805, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1161 | h1161
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1162 | h1162
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                · linarith only [h1163, h805, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h1061, h1165, h805, hc14, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                    · linarith only [h0, h1161, h1163, h1167, h802, h805, hc12, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1169 | h1169
                      · linarith only [h0, h1061, h1162, h1169, h802, h805, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1171 | h1171
                        · linarith only [h1061, h1171, h805, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · linarith only [h1171, h805, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h1162, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1161, h802, h805, hc23, hlam, hphi, ht01, ht12, u0ehi7]
      · linarith only [h0, h802, h804, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1177 | h1177
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1178 | h1178
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1179 | h1179
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1180 | h1180
            · linarith only [h0, h1180, h803, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1179, h1180, h802, hc23, hlam, hphi, ht01, ht12, u0ehi9]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1183 | h1183
            · linarith only [h0, h1183, h803, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1183, h802, hc23, hlam, hphi, ht01, ht12, u0ehi8]
        · linarith only [h0, h1178, h802, h803, hlam]
      · linarith only [h0, h1177, h802, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1188 | h1188
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1189 | h1189
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1190 | h1190
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1191 | h1191
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1192 | h1192
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1193 | h1193
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1194 | h1194
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1195 | h1195
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1196 | h1196
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1197 | h1197
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1198 | h1198
                        · linarith only [h1188, h1196, h1198, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1188, h1196, h1197, h1198, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1201 | h1201
                        · linarith only [h1188, h1190, h1197, h1201, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases h4bigk with h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c | h1203c
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h802, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            rcases p1203_3 (m.d 0 4) (by simp) with h1206 | h1206
                            · rcases p1203_3 (m.d 1 4) (by simp) with h1207 | h1207
                              · rcases p1203_3 (m.d 2 4) (by simp) with h1208 | h1208
                                · linarith only [h1189, h1208, hlam]
                                · rcases p1203_3 (m.d 3 4) (by simp) with h1210 | h1210
                                  · linarith only [h1190, h1210, hlam]
                                  · rcases p1203_3 (m.d 4 5) (by simp) with h1212 | h1212
                                    · linarith only [h1191, h1212, hlam]
                                    · linarith only [h1197, h1212, hlam]
                              · linarith only [h1193, h1207, hlam]
                            · linarith only [h1189, h1206, hlam]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            rcases p1203_3 (m.d 0 4) (by simp) with h1217 | h1217
                            · rcases p1203_3 (m.d 1 4) (by simp) with h1218 | h1218
                              · rcases p1203_3 (m.d 2 4) (by simp) with h1219 | h1219
                                · linarith only [h1189, h1219, hlam]
                                · linarith only [h1196, h1219, hlam]
                              · linarith only [h1194, h1218, hlam]
                            · linarith only [h1190, h1217, hlam]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1188, h1190, h1196, h1197, hc34, hlam, hphi, ht0b, ht45, ht5b, p1203_1, u0elo1]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1192, h1194, h802, hc12, hlam, hphi, ht01, p1203_1, u0ehi5]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            rcases p1203_3 (m.d 0 4) (by simp) with h1227 | h1227
                            · linarith only [h1227, h802, hlam]
                            · linarith only [h1189, h1227, hlam]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            rcases p1203_3 (m.d 0 4) (by simp) with h1230 | h1230
                            · linarith only [h1230, h802, hlam]
                            · linarith only [h1190, h1230, hlam]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            rcases p1203_3 (m.d 0 4) (by simp) with h1233 | h1233
                            · linarith only [h1233, h802, hlam]
                            · linarith only [h1191, h1233, hlam]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1189, hlam, p1203_1]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1193, hlam, p1203_1]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1191, h1197, hc34, hlam, hphi, ht0b, ht45, ht5b, p1203_1, u0elo3]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1197, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1190, hlam, p1203_1]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1194, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1196, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1201, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1191, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1195, hlam, p1203_0]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1191, hc24, hlam, hphi, ht0b, ht45, ht5b, p1203_1, u0elo3]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [h1188, h1190, h1191, hc34, hlam, hphi, ht0b, ht45, ht5b, p1203_1, u0elo1]
                          · have p1203_0 := h1203c.1
                            have p1203_1 := h1203c.2.1
                            have p1203_2 := h1203c.2.2.1
                            have p1203_3 := h1203c.2.2.2
                            linarith only [hlam, p1203_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1252 | h1252
                        · rcases h4bigk with h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h802, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1188, h1190, h1251, hc45, hlam, hphi, ht0b, ht5b, p1253_1, u0elo1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1188, h1190, h1196, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1253_1, u0elo1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            rcases p1253_3 (m.d 0 4) (by simp) with h1258 | h1258
                            · rcases p1253_3 (m.d 1 4) (by simp) with h1259 | h1259
                              · rcases p1253_3 (m.d 2 4) (by simp) with h1260 | h1260
                                · linarith only [h1189, h1260, hlam]
                                · linarith only [h1251, h1260, hlam]
                              · linarith only [h1195, h1259, hlam]
                            · linarith only [h1258, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1192, h1194, hc12, hlam, hphi, ht01, p1253_1, u0ehi8]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            rcases p1253_3 (m.d 0 4) (by simp) with h1267 | h1267
                            · linarith only [h1267, h802, hlam]
                            · linarith only [h1189, h1267, hlam]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            rcases p1253_3 (m.d 0 4) (by simp) with h1270 | h1270
                            · linarith only [h1270, h802, hlam]
                            · linarith only [h1190, h1270, hlam]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            rcases p1253_3 (m.d 0 4) (by simp) with h1273 | h1273
                            · linarith only [h1273, h802, hlam]
                            · linarith only [h1191, h1273, hlam]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1189, hlam, p1253_1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1193, hlam, p1253_1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1196, hlam, p1253_1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1189, hc45, hlam, hphi, ht0b, ht5b, p1253_1, u0elo1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1190, hlam, p1253_1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1194, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1188, h1190, hc24, hlam, hphi, ht0b, ht45, ht5b, p1253_1, u0elo1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1188, h1190, hc45, hlam, hphi, ht0b, ht5b, p1253_1, u0elo1]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1191, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1195, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1251, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [h1252, hlam, p1253_0]
                          · have p1253_0 := h1253c.1
                            have p1253_1 := h1253c.2.1
                            have p1253_2 := h1253c.2.2.1
                            have p1253_3 := h1253c.2.2.2
                            linarith only [hlam, p1253_0]
                        · linarith only [h1189, h1251, h1252, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1292 | h1292
                        · linarith only [h1188, h1190, h1196, h1251, h1292, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h1191, h1196, h1292, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1188, h1190, h1191, h1195, h802, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h1188, h1190, h1194, h802, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1193, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1192, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1302 | h1302
                  · linarith only [h1191, h1299, h1301, h1302, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h1302, h802, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                · linarith only [h1190, h1301, h802, hlam, hphi, u0ehi5, u0elo2]
              · linarith only [h0, h1189, h1300, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1299, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1308 | h1308
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1310 | h1310
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                · linarith only [h1190, h1311, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1313 | h1313
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1314 | h1314
                    · linarith only [h1188, h1311, h1314, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1316 | h1316
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1317 | h1317
                        · rcases h4bigk with h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c | h1318c
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h802, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1316, hc45, hlam, hphi, ht0b, ht5b, p1318_1, u0elo3]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1190, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 4) (by simp) with h1323 | h1323
                            · rcases p1318_3 (m.d 1 4) (by simp) with h1324 | h1324
                              · rcases p1318_3 (m.d 2 4) (by simp) with h1325 | h1325
                                · linarith only [h1189, h1325, hlam]
                                · linarith only [h1316, h1325, hlam]
                              · linarith only [h1313, h1324, hlam]
                            · linarith only [h1323, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1310, hc12, hlam, hphi, ht01, p1318_1, u0ehi8]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 4) (by simp) with h1332 | h1332
                            · linarith only [h1332, h802, hlam]
                            · linarith only [h1189, h1332, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1311, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 4) (by simp) with h1336 | h1336
                            · linarith only [h1336, h802, hlam]
                            · linarith only [h1308, h1336, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1189, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1310, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1314, hlam, p1318_1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1189, hc45, hlam, hphi, ht0b, ht5b, p1318_1, u0elo1]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1308, hc34, hlam, hphi, ht01, ht12, ht23, p1318_1, u0ehi9]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h802, hc34, hlam, hphi, ht01, ht12, ht23, p1318_1, u0ehi5]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 4) (by simp) with h1346 | h1346
                            · linarith only [h1190, h1346, hlam]
                            · linarith only [h1189, h1346, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            rcases p1318_3 (m.d 0 4) (by simp) with h1350 | h1350
                            · linarith only [h1190, h1350, hlam]
                            · linarith only [h1308, h1350, hlam]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1308, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1313, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1316, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [h1317, hlam, p1318_0]
                          · have p1318_0 := h1318c.1
                            have p1318_1 := h1318c.2.1
                            have p1318_2 := h1318c.2.2.1
                            have p1318_3 := h1318c.2.2.2
                            linarith only [hlam, p1318_0]
                        · linarith only [h1189, h1316, h1317, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1359 | h1359
                        · rcases h4bigk with h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c | h1360c
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h802, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            rcases p1360_3 (m.d 0 4) (by simp) with h1363 | h1363
                            · rcases p1360_3 (m.d 1 4) (by simp) with h1364 | h1364
                              · rcases p1360_3 (m.d 2 4) (by simp) with h1365 | h1365
                                · linarith only [h1189, h1365, hlam]
                                · rcases p1360_3 (m.d 3 4) (by simp) with h1367 | h1367
                                  · rcases p1360_3 (m.d 4 5) (by simp) with h1368 | h1368
                                    · linarith only [h1308, h1368, hlam]
                                    · linarith only [h1316, h1368, hlam]
                                  · linarith only [h1314, h1367, hlam]
                              · linarith only [h1310, h1364, hlam]
                            · linarith only [h1189, h1363, hlam]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1190, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1189, h1314, h1316, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1360_1, u0elo1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, p1360_1, u0ehi8]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            rcases p1360_3 (m.d 0 4) (by simp) with h1378 | h1378
                            · linarith only [h1378, h802, hlam]
                            · linarith only [h1189, h1378, hlam]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1311, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1311, h1314, h1316, hc23, hc34, hlam, hphi, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1189, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1310, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1314, hlam, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1316, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1308, h1314, h1316, hc23, hc34, hlam, hphi, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h802, hc34, hlam, hphi, ht01, ht12, ht23, p1360_1, u0ehi5]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            rcases p1360_3 (m.d 0 4) (by simp) with h1390 | h1390
                            · linarith only [h1190, h1390, hlam]
                            · linarith only [h1189, h1390, hlam]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1314, h1316, hc23, hc34, hlam, hphi, p1360_1]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1308, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1313, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1308, h1314, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1360_1, u0elo3]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [h1359, hlam, p1360_0]
                          · have p1360_0 := h1360c.1
                            have p1360_1 := h1360c.2.1
                            have p1360_2 := h1360c.2.2.1
                            have p1360_3 := h1360c.2.2.2
                            linarith only [hlam, p1360_0]
                        · linarith only [h1189, h1190, h1308, h1359, hlam, hphi, u0ehi7, u0elo1]
                  · linarith only [h1189, h1308, h1313, h802, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h0, h1310, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1309, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1404 | h1404
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1405 | h1405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1406 | h1406
                · linarith only [h1190, h1406, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1408 | h1408
                  · linarith only [h1308, h1405, h1408, hc12, hlam, hphi, ht01, u0ehi8]
                  · linarith only [h1408, h802, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
              · linarith only [h0, h1189, h1405, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h1188, h1404, hlam, hphi, u0ehi5, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1413 | h1413
        · linarith only [h1188, h1189, h1413, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1415 | h1415
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1416 | h1416
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1417 | h1417
              · linarith only [h1189, h1417, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1417, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1188, h1416, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1421 | h1421
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1422 | h1422
              · linarith only [h1189, h1422, hc12, hlam, hphi, ht01, u0ehi6]
              · linarith only [h0, h1422, hc24, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h1188, h1421, hlam, hphi, u0ehi5, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1426 | h1426
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1427 | h1427
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1428 | h1428
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
            · linarith only [h1188, h1426, h1429, h802, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1429, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1432 | h1432
            · linarith only [h1188, h1426, h1432, h802, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1432, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · linarith only [h1188, h1426, h1427, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1436 | h1436
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1437 | h1437
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1438 | h1438
            · linarith only [h0, h1188, h1438, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1438, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1441 | h1441
            · linarith only [h0, h1188, h1441, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1441, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1444 | h1444
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
            · linarith only [h0, h1188, h1445, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1445, hc23, hlam, hphi, ht01, ht12, u0ehi5]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1448 | h1448
            · linarith only [h0, h1188, h1448, hc12, hlam, hphi, ht01, u0ehi5]
            · linarith only [h0, h1448, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_12_14_M_LR_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_M_LR_L_I_L_I_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_M_LR_L_I_L_I_x1 m hb0 hb2 hb4 h0

end R2N4
