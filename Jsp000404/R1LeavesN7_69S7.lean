import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_69S6

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_25_L_R_L_R_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h791 | h791
  · linarith only [h0, h791, hc12, hlam, hphi, u1ehi2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h793 | h793
    · linarith only [h0, h793, hc12, hlam, hphi, u1ehi3]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h795 | h795
      · linarith only [h0, h795, hc12, hlam, hphi, u1ehi4]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h797 | h797
        · rcases m.htr 0 2 4 (by decide) (by decide) with h798 | h798
          · rcases m.htr 0 2 5 (by decide) (by decide) with h799 | h799
            · rcases m.htr 0 3 4 (by decide) (by decide) with h800 | h800
              · rcases m.htr 0 3 5 (by decide) (by decide) with h801 | h801
                · rcases m.htr 0 4 5 (by decide) (by decide) with h802 | h802
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h803 | h803
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h805 | h805
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h806 | h806
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h807 | h807
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h808 | h808
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h809 | h809
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h810 | h810
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h811 | h811
                                    · rcases h5bigk with h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c | h812c
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h795, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h797, h800, h802, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p812_1, u2ehi4]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 5) (by simp) with h816 | h816
                                        · rcases p812_3 (m.d 1 5) (by simp) with h817 | h817
                                          · rcases p812_3 (m.d 2 5) (by simp) with h818 | h818
                                            · linarith only [h799, h818, hlam]
                                            · linarith only [h809, h818, hlam]
                                          · linarith only [h806, h817, hlam]
                                        · linarith only [h801, h816, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 5) (by simp) with h823 | h823
                                        · rcases p812_3 (m.d 1 5) (by simp) with h824 | h824
                                          · rcases p812_3 (m.d 2 5) (by simp) with h825 | h825
                                            · linarith only [h799, h825, hlam]
                                            · linarith only [h810, h825, hlam]
                                          · linarith only [h807, h824, hlam]
                                        · linarith only [h802, h823, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p812_1, u1ehi0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h803, h805, h807, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p812_1, u2ehi4]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 5) (by simp) with h833 | h833
                                        · linarith only [h795, h833, hlam]
                                        · linarith only [h801, h833, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        rcases p812_3 (m.d 0 5) (by simp) with h836 | h836
                                        · linarith only [h795, h836, hlam]
                                        · linarith only [h802, h836, hlam]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h799, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h804, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, h799, h811, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, h797, h808, h810, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h801, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h806, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h809, hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h0, h797, h801, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h802, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h807, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h810, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [h811, hlam, p812_1]
                                      · have p812_0 := h812c.1
                                        have p812_1 := h812c.2.1
                                        have p812_2 := h812c.2.2.1
                                        have p812_3 := h812c.2.2.2
                                        linarith only [hlam, p812_0]
                                    · rcases h5bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h795, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p854_1, u2ehi4]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        rcases p854_3 (m.d 0 5) (by simp) with h858 | h858
                                        · rcases p854_3 (m.d 1 5) (by simp) with h859 | h859
                                          · rcases p854_3 (m.d 2 5) (by simp) with h860 | h860
                                            · linarith only [h799, h860, hlam]
                                            · linarith only [h809, h860, hlam]
                                          · linarith only [h806, h859, hlam]
                                        · linarith only [h801, h858, hlam]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h795, h803, h805, h807, h811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p854_1, u1ehi0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h803, h805, h807, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p854_1, u2ehi4]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        rcases p854_3 (m.d 0 5) (by simp) with h869 | h869
                                        · linarith only [h795, h869, hlam]
                                        · linarith only [h801, h869, hlam]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h803, h805, h807, h811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h799, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h804, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h0, h799, h811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h0, h797, h808, h810, h811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h801, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h806, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h809, hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h811, hlam, p854_0]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h802, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h807, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h810, hlam, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [h811, hc34, hc45, hlam, hphi, p854_1]
                                      · have p854_0 := h854c.1
                                        have p854_1 := h854c.2.1
                                        have p854_2 := h854c.2.2.1
                                        have p854_3 := h854c.2.2.2
                                        linarith only [hlam, p854_0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h888 | h888
                                    · linarith only [h810, h888, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h5bigk with h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c | h890c
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h795, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p890_1, u2ehi4]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        rcases p890_3 (m.d 0 5) (by simp) with h894 | h894
                                        · rcases p890_3 (m.d 1 5) (by simp) with h895 | h895
                                          · rcases p890_3 (m.d 2 5) (by simp) with h896 | h896
                                            · linarith only [h799, h896, hlam]
                                            · linarith only [h809, h896, hlam]
                                          · linarith only [h806, h895, hlam]
                                        · linarith only [h801, h894, hlam]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h795, h803, h805, h807, h810, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p890_1, u2ehi3]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p890_1, u1ehi0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h803, h805, h807, h810, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p890_1, u2ehi3]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        rcases p890_3 (m.d 0 5) (by simp) with h905 | h905
                                        · linarith only [h795, h905, hlam]
                                        · linarith only [h801, h905, hlam]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h803, h805, h807, h810, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p890_1, u2ehi3]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h799, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h804, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h0, h799, h888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h810, hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h801, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h806, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h809, hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h888, hlam, p890_0]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h802, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h807, hlam, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hc45, hlam, hphi, ht23, ht34, p890_1, u2ehi4]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [h0, h797, h800, h802, h888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p890_1]
                                      · have p890_0 := h890c.1
                                        have p890_1 := h890c.2.1
                                        have p890_2 := h890c.2.2.1
                                        have p890_3 := h890c.2.2.2
                                        linarith only [hlam, p890_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h924 | h924
                                  · linarith only [h808, h809, h924, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h926 | h926
                                    · linarith only [h924, h926, hc34, hlam, hphi, ht23, u2ehi3]
                                    · rcases h5bigk with h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c | h928c
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h795, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h808, h809, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h795, h803, h805, h807, h808, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h795, h803, h805, h807, h808, h809, h926, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p928_1, u1ehi0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h803, h805, h807, h808, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h803, h805, h807, h808, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h803, h805, h807, h808, h809, h926, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h799, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h804, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h809, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h924, hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h801, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h806, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h797, h800, h802, h808, h809, h926, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h926, hlam, p928_0]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h802, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h807, hlam, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h0, h797, h800, h802, h808, h809, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p928_1, u2ehi3]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [h0, h797, h800, h802, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p928_1]
                                      · have p928_0 := h928c.1
                                        have p928_1 := h928c.2.1
                                        have p928_2 := h928c.2.2.1
                                        have p928_3 := h928c.2.2.2
                                        linarith only [hlam, p928_0]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h954 | h954
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h955 | h955
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h956 | h956
                                    · rcases h5bigk with h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c | h957c
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h795, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p957_1, u2ehi4]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 5) (by simp) with h961 | h961
                                        · rcases p957_3 (m.d 1 5) (by simp) with h962 | h962
                                          · rcases p957_3 (m.d 2 5) (by simp) with h963 | h963
                                            · linarith only [h799, h963, hlam]
                                            · linarith only [h954, h963, hlam]
                                          · linarith only [h806, h962, hlam]
                                        · linarith only [h801, h961, hlam]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 5) (by simp) with h968 | h968
                                        · rcases p957_3 (m.d 1 5) (by simp) with h969 | h969
                                          · rcases p957_3 (m.d 2 5) (by simp) with h970 | h970
                                            · linarith only [h799, h970, hlam]
                                            · linarith only [h955, h970, hlam]
                                          · linarith only [h807, h969, hlam]
                                        · linarith only [h802, h968, hlam]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p957_1, u1ehi0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h803, h805, h807, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p957_1, u2ehi4]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 5) (by simp) with h978 | h978
                                        · linarith only [h795, h978, hlam]
                                        · linarith only [h801, h978, hlam]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        rcases p957_3 (m.d 0 5) (by simp) with h981 | h981
                                        · linarith only [h795, h981, hlam]
                                        · linarith only [h802, h981, hlam]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h799, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h804, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h0, h797, h954, h956, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h0, h797, h800, h808, h954, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h801, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h806, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h954, hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h0, h797, h801, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h802, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h807, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h955, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [h956, hlam, p957_1]
                                      · have p957_0 := h957c.1
                                        have p957_1 := h957c.2.1
                                        have p957_2 := h957c.2.2.1
                                        have p957_3 := h957c.2.2.2
                                        linarith only [hlam, p957_0]
                                    · linarith only [h808, h956, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                  · linarith only [h808, h954, h955, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1001 | h1001
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1002 | h1002
                                    · rcases h5bigk with h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c | h1003c
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [hlam, p1003_0]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h795, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h954, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h954, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        rcases p1003_3 (m.d 0 5) (by simp) with h1008 | h1008
                                        · rcases p1003_3 (m.d 1 5) (by simp) with h1009 | h1009
                                          · rcases p1003_3 (m.d 2 5) (by simp) with h1010 | h1010
                                            · linarith only [h1010, h799, hlam]
                                            · linarith only [h1001, h1010, hlam]
                                          · linarith only [h1009, h807, hlam]
                                        · linarith only [h1008, h802, hlam]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h795, h803, h805, h807, hc12, hlam, hphi, p1003_1, u1ehi0]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [hlam, p1003_0]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h803, h805, h807, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h803, h805, h807, h954, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1003_1, u2ehi2]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        rcases p1003_3 (m.d 0 5) (by simp) with h1019 | h1019
                                        · linarith only [h1019, h795, hlam]
                                        · linarith only [h1019, h802, hlam]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h799, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h804, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [hlam, p1003_0]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h954, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h0, h1001, h798, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h801, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h806, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h0, h797, h801, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [hlam, p1003_0]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h0, h1002, h797, h800, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h802, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h807, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h1001, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [h1002, hlam, p1003_1]
                                      · have p1003_0 := h1003c.1
                                        have p1003_1 := h1003c.2.1
                                        have p1003_2 := h1003c.2.2.1
                                        have p1003_3 := h1003c.2.2.2
                                        linarith only [hlam, p1003_0]
                                    · linarith only [h1002, h793, h802, h803, h805, h808, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1038 | h1038
                                    · linarith only [h0, h1001, h1038, h797, h800, h808, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h1038, h808, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                            · linarith only [h793, h802, h807, hlam]
                          · linarith only [h791, h806, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h791, h805, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h791, h803, h804, hc25, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h799, h803, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1046 | h1046
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1047 | h1047
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1048 | h1048
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1050 | h1050
                            · linarith only [h1046, h1048, h1050, h793, h802, hc12, hlam, hphi, u1ehi0]
                            · linarith only [h1050, h793, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h0, h1049, h797, h801, hc12, hlam, hphi, u1ehi2]
                        · linarith only [h1048, h791, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1047, h797, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1046, h799, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1057 | h1057
                  · linarith only [h1057, h800, h801, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1061 | h1061
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1062 | h1062
                          · linarith only [h1059, h1062, h791, h801, hc12, hlam, hphi, u1ehi0]
                          · linarith only [h1062, h791, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h1061, h791, h800, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                      · linarith only [h0, h1060, h799, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h1059, h797, h801, hc35, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1068 | h1068
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1069 | h1069
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1070 | h1070
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1071 | h1071
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1072 | h1072
                        · linarith only [h1070, h1072, h791, h800, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1072, h791, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1071, h799, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h1070, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1068, h1069, h800, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1078 | h1078
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1079 | h1079
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1080 | h1080
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                        · linarith only [h1079, h1081, h791, h800, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1081, h791, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1080, hc25, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h1079, h799, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1087 | h1087
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                        · linarith only [h1086, h1088, h791, h800, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h1088, h791, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h1087, h799, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                    · linarith only [h0, h1086, h799, hc23, hlam, hphi, u2ehi4]
            · linarith only [h797, h799, hc25, hlam, hphi, u2ehi2]
          · linarith only [h797, h798, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1095 | h1095
          · linarith only [h1095, h797, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1097 | h1097
            · linarith only [h1097, h797, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1099 | h1099
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1100 | h1100
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
                    · linarith only [h0, h1102, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1102, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
                    · linarith only [h0, h1105, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1105, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1108 | h1108
                  · linarith only [h1099, h1100, h1108, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1110 | h1110
                    · linarith only [h0, h1110, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1110, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1114 | h1114
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1115 | h1115
                    · linarith only [h0, h1115, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1115, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h1099, h1113, h1114, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1119 | h1119
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1120 | h1120
                    · linarith only [h0, h1120, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1120, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1123 | h1123
                    · linarith only [h0, h1123, h797, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h1123, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_11_12_25_L_R_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h1ehi := hb1.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_25_L_R_L_R_H_I_x0 m hb1 hb2 hb5 h0
  · exact r1l7_11_12_25_L_R_L_R_H_I_x1 m hb1 hb2 hb5 h0

end R2N4
