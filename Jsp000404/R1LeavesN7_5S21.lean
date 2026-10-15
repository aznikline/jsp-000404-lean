import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h11849 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 1 2 3 (by decide) (by decide) with h12809 | h12809
  · rcases m.htr 1 2 4 (by decide) (by decide) with h12810 | h12810
    · rcases m.htr 1 2 5 (by decide) (by decide) with h12811 | h12811
      · rcases m.htr 1 3 4 (by decide) (by decide) with h12812 | h12812
        · rcases m.htr 1 3 5 (by decide) (by decide) with h12813 | h12813
          · rcases m.htr 1 4 5 (by decide) (by decide) with h12814 | h12814
            · rcases m.htr 2 3 4 (by decide) (by decide) with h12815 | h12815
              · rcases m.htr 2 3 5 (by decide) (by decide) with h12816 | h12816
                · rcases m.htr 2 4 5 (by decide) (by decide) with h12817 | h12817
                  · linarith only [h11845, h11849, h12817, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h12819 | h12819
                    · linarith only [h11844, h11849, h12815, h12819, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases h0bigk with h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c | h12821c
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h0, hlam, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h6310, hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h9935, hlam, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11282, hlam, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12827 | h12827
                        · linarith only [h0, h12827, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12829 | h12829
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12830 | h12830
                            · linarith only [h11844, h12830, hlam]
                            · linarith only [h12830, h6310, hlam]
                          · linarith only [h0, h12829, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11844, h12816, h12819, hc34, hlam, hphi, ht0b, ht45, ht5b, p12821_1, u0elo1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12836 | h12836
                        · linarith only [h0, h12836, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12838 | h12838
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12839 | h12839
                            · linarith only [h11844, h12839, hlam]
                            · linarith only [h11847, h12839, hlam]
                          · linarith only [h11845, h12838, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12843 | h12843
                        · linarith only [h0, h12843, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12845 | h12845
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12846 | h12846
                            · linarith only [h11844, h12846, hlam]
                            · linarith only [h11848, h12846, hlam]
                          · linarith only [h11846, h12845, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12850 | h12850
                        · linarith only [h12850, h6310, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12852 | h12852
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12853 | h12853
                            · rcases p12821_3 (m.d 0 4) (by simp) with h12854 | h12854
                              · linarith only [h11847, h12854, hlam]
                              · linarith only [h12854, h9935, hlam]
                            · linarith only [h12853, h6310, hlam]
                          · linarith only [h0, h12852, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11844, hlam, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12861 | h12861
                        · linarith only [h12861, h6310, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12863 | h12863
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12864 | h12864
                            · rcases p12821_3 (m.d 0 4) (by simp) with h12865 | h12865
                              · linarith only [h11847, h12865, hlam]
                              · rcases p12821_3 (m.d 0 5) (by simp) with h12867 | h12867
                                · linarith only [h11848, h12867, hlam]
                                · linarith only [h11849, h12867, hlam]
                            · linarith only [h11847, h12864, hlam]
                          · linarith only [h11845, h12863, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        rcases p12821_3 (m.d 0 1) (by simp) with h12872 | h12872
                        · linarith only [h12872, h6310, hlam]
                        · rcases p12821_3 (m.d 0 2) (by simp) with h12874 | h12874
                          · rcases p12821_3 (m.d 0 3) (by simp) with h12875 | h12875
                            · rcases p12821_3 (m.d 0 4) (by simp) with h12876 | h12876
                              · linarith only [h11847, h12876, hlam]
                              · rcases p12821_3 (m.d 0 5) (by simp) with h12878 | h12878
                                · linarith only [h11848, h12878, hlam]
                                · rcases h0emin with h12880 | h12880 | h12880 | h12880 | h12880
                                  · linarith only [h11844, h11849, h12880, h9935, hlam, p12821_1, u0elo1]
                                  · rcases h1bigk with h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c | h12882c
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h0, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h6310, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h9935, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h11282, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      rcases p12882_3 (m.d 0 1) (by simp) with h12888 | h12888
                                      · linarith only [h12888, hlam, p12882_0]
                                      · rcases p12882_3 (m.d 1 2) (by simp) with h12890 | h12890
                                        · rcases p12882_3 (m.d 1 3) (by simp) with h12891 | h12891
                                          · linarith only [h12809, h12891, hlam]
                                          · linarith only [h12891, h6310, hlam]
                                        · linarith only [h12890, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      rcases p12882_3 (m.d 0 1) (by simp) with h12899 | h12899
                                      · linarith only [h12899, hlam, p12882_0]
                                      · rcases p12882_3 (m.d 1 2) (by simp) with h12901 | h12901
                                        · rcases p12882_3 (m.d 1 3) (by simp) with h12902 | h12902
                                          · rcases p12882_3 (m.d 1 4) (by simp) with h12903 | h12903
                                            · linarith only [h12812, h12903, hlam]
                                            · linarith only [h12903, h9935, hlam]
                                          · linarith only [h12902, hlam, p12882_0]
                                        · linarith only [h0, h12901, hlam]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12809, hlam, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h11849, h12814, h9935, hc01, hc13, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h11849, h12809, h12814, h9935, hc01, hc12, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      rcases p12882_3 (m.d 0 1) (by simp) with h12912 | h12912
                                      · linarith only [h12912, hlam, p12882_0]
                                      · rcases p12882_3 (m.d 1 2) (by simp) with h12914 | h12914
                                        · rcases p12882_3 (m.d 1 3) (by simp) with h12915 | h12915
                                          · rcases p12882_3 (m.d 1 4) (by simp) with h12916 | h12916
                                            · rcases p12882_3 (m.d 1 5) (by simp) with h12917 | h12917
                                              · linarith only [h12814, h12917, hlam]
                                              · linarith only [h11282, h12917, hlam]
                                            · linarith only [h12916, hlam, p12882_0]
                                          · linarith only [h12915, h6310, hlam]
                                        · linarith only [h0, h12914, hlam]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12810, hlam, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12812, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h11849, h12814, h9935, hc01, hc14, hlam, hphi, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      rcases p12882_3 (m.d 0 1) (by simp) with h12927 | h12927
                                      · linarith only [h12927, hlam, p12882_0]
                                      · rcases p12882_3 (m.d 1 2) (by simp) with h12929 | h12929
                                        · rcases p12882_3 (m.d 1 3) (by simp) with h12930 | h12930
                                          · rcases p12882_3 (m.d 1 4) (by simp) with h12931 | h12931
                                            · rcases p12882_3 (m.d 1 5) (by simp) with h12932 | h12932
                                              · rcases h3bigk with h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c | h12933c
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h6310, hlam, p12933_1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11844, h12816, h12819, hc34, hlam, hphi, ht0b, ht45, ht5b, p12933_1, u0elo1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  rcases p12933_3 (m.d 0 3) (by simp) with h12937 | h12937
                                                  · rcases p12933_3 (m.d 1 3) (by simp) with h12938 | h12938
                                                    · rcases p12933_3 (m.d 2 3) (by simp) with h12939 | h12939
                                                      · linarith only [h11844, h12939, hlam]
                                                      · linarith only [h12815, h12939, hlam]
                                                    · linarith only [h12812, h12938, hlam]
                                                  · linarith only [h12937, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  rcases p12933_3 (m.d 0 3) (by simp) with h12944 | h12944
                                                  · rcases p12933_3 (m.d 1 3) (by simp) with h12945 | h12945
                                                    · rcases p12933_3 (m.d 2 3) (by simp) with h12946 | h12946
                                                      · linarith only [h11844, h12946, hlam]
                                                      · linarith only [h12816, h12946, hlam]
                                                    · linarith only [h12813, h12945, hlam]
                                                  · linarith only [h12944, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11849, h12809, h9935, hc01, hc12, hlam, hphi, p12821_1, p12933_1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  rcases p12933_3 (m.d 0 3) (by simp) with h12953 | h12953
                                                  · linarith only [h12953, h6310, hlam]
                                                  · linarith only [h11844, h12953, hlam]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  rcases p12933_3 (m.d 0 3) (by simp) with h12956 | h12956
                                                  · linarith only [h12956, h6310, hlam]
                                                  · linarith only [h11847, h12956, hlam]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  rcases p12933_3 (m.d 0 3) (by simp) with h12959 | h12959
                                                  · linarith only [h12959, h6310, hlam]
                                                  · linarith only [h11848, h12959, hlam]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11844, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12809, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p12933_1, u0elo1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11844, h12819, hc34, hlam, hphi, ht0b, ht45, ht5b, p12933_1, u0elo1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11847, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12812, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12815, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12819, hlam, p12933_1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11848, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12813, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h12816, hlam, p12933_0]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [h11844, h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p12933_1, u0elo1]
                                                · have p12933_0 := h12933c.1
                                                  have p12933_1 := h12933c.2.1
                                                  have p12933_2 := h12933c.2.2.1
                                                  have p12933_3 := h12933c.2.2.2
                                                  linarith only [hlam, p12933_0]
                                              · linarith only [h12932, hlam, p12882_0]
                                            · linarith only [h12931, h9935, hlam]
                                          · linarith only [h12930, h6310, hlam]
                                        · linarith only [h0, h12929, hlam]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12811, hlam, p12882_1]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12813, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [h12814, hlam, p12882_0]
                                    · have p12882_0 := h12882c.1
                                      have p12882_1 := h12882c.2.1
                                      have p12882_2 := h12882c.2.2.1
                                      have p12882_3 := h12882c.2.2.2
                                      linarith only [hlam, p12882_0]
                                  · rcases h1bigk with h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c | h12985c
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h0, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h6310, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h9935, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h11282, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      rcases p12985_3 (m.d 0 1) (by simp) with h12991 | h12991
                                      · linarith only [h12991, hlam, p12985_0]
                                      · rcases p12985_3 (m.d 1 2) (by simp) with h12993 | h12993
                                        · rcases p12985_3 (m.d 1 3) (by simp) with h12994 | h12994
                                          · linarith only [h12809, h12994, hlam]
                                          · linarith only [h12994, h6310, hlam]
                                        · linarith only [h12993, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      rcases p12985_3 (m.d 0 1) (by simp) with h13002 | h13002
                                      · linarith only [h13002, hlam, p12985_0]
                                      · rcases p12985_3 (m.d 1 2) (by simp) with h13004 | h13004
                                        · rcases p12985_3 (m.d 1 3) (by simp) with h13005 | h13005
                                          · rcases p12985_3 (m.d 1 4) (by simp) with h13006 | h13006
                                            · linarith only [h12812, h13006, hlam]
                                            · linarith only [h13006, h9935, hlam]
                                          · linarith only [h13005, hlam, p12985_0]
                                        · linarith only [h0, h13004, hlam]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12809, hlam, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h11849, h12814, h9935, hc01, hc13, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h11849, h12809, h12814, h9935, hc01, hc12, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      rcases p12985_3 (m.d 0 1) (by simp) with h13015 | h13015
                                      · linarith only [h13015, hlam, p12985_0]
                                      · rcases p12985_3 (m.d 1 2) (by simp) with h13017 | h13017
                                        · rcases p12985_3 (m.d 1 3) (by simp) with h13018 | h13018
                                          · rcases p12985_3 (m.d 1 4) (by simp) with h13019 | h13019
                                            · rcases p12985_3 (m.d 1 5) (by simp) with h13020 | h13020
                                              · linarith only [h12814, h13020, hlam]
                                              · linarith only [h11282, h13020, hlam]
                                            · linarith only [h13019, hlam, p12985_0]
                                          · linarith only [h13018, h6310, hlam]
                                        · linarith only [h0, h13017, hlam]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12810, hlam, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12812, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h11849, h12814, h9935, hc01, hc14, hlam, hphi, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      rcases p12985_3 (m.d 0 1) (by simp) with h13030 | h13030
                                      · linarith only [h13030, hlam, p12985_0]
                                      · rcases p12985_3 (m.d 1 2) (by simp) with h13032 | h13032
                                        · rcases p12985_3 (m.d 1 3) (by simp) with h13033 | h13033
                                          · rcases p12985_3 (m.d 1 4) (by simp) with h13034 | h13034
                                            · rcases p12985_3 (m.d 1 5) (by simp) with h13035 | h13035
                                              · rcases h3bigk with h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c | h13036c
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h6310, hlam, p13036_1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11844, h12815, hc34, hlam, hphi, ht0b, ht45, ht5b, p13036_1, u0elo1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  rcases p13036_3 (m.d 0 3) (by simp) with h13040 | h13040
                                                  · rcases p13036_3 (m.d 1 3) (by simp) with h13041 | h13041
                                                    · rcases p13036_3 (m.d 2 3) (by simp) with h13042 | h13042
                                                      · linarith only [h11844, h13042, hlam]
                                                      · linarith only [h12815, h13042, hlam]
                                                    · linarith only [h12812, h13041, hlam]
                                                  · linarith only [h13040, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  rcases p13036_3 (m.d 0 3) (by simp) with h13047 | h13047
                                                  · rcases p13036_3 (m.d 1 3) (by simp) with h13048 | h13048
                                                    · rcases p13036_3 (m.d 2 3) (by simp) with h13049 | h13049
                                                      · linarith only [h11844, h13049, hlam]
                                                      · linarith only [h12816, h13049, hlam]
                                                    · linarith only [h12813, h13048, hlam]
                                                  · linarith only [h13047, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11849, h12809, h9935, hc01, hc12, hlam, hphi, p12821_1, p13036_1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  rcases p13036_3 (m.d 0 3) (by simp) with h13056 | h13056
                                                  · linarith only [h13056, h6310, hlam]
                                                  · linarith only [h11844, h13056, hlam]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  rcases p13036_3 (m.d 0 3) (by simp) with h13059 | h13059
                                                  · linarith only [h13059, h6310, hlam]
                                                  · linarith only [h11847, h13059, hlam]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  rcases p13036_3 (m.d 0 3) (by simp) with h13062 | h13062
                                                  · linarith only [h13062, h6310, hlam]
                                                  · linarith only [h11848, h13062, hlam]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11844, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12809, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11844, hc34, hlam, hphi, ht0b, ht45, ht5b, p13036_1, u0elo1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11844, h12819, hc34, hlam, hphi, ht0b, ht45, ht5b, p13036_1, u0elo1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11847, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12812, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12815, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12819, hlam, p13036_1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11848, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12813, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h12816, hlam, p13036_0]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [h11844, h11848, hc34, hlam, hphi, ht0b, ht45, ht5b, p13036_1, u0elo1]
                                                · have p13036_0 := h13036c.1
                                                  have p13036_1 := h13036c.2.1
                                                  have p13036_2 := h13036c.2.2.1
                                                  have p13036_3 := h13036c.2.2.2
                                                  linarith only [hlam, p13036_0]
                                              · linarith only [h13035, hlam, p12985_0]
                                            · linarith only [h13034, h9935, hlam]
                                          · linarith only [h13033, h6310, hlam]
                                        · linarith only [h0, h13032, hlam]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12811, hlam, p12985_1]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12813, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [h12814, hlam, p12985_0]
                                    · have p12985_0 := h12985c.1
                                      have p12985_1 := h12985c.2.1
                                      have p12985_2 := h12985c.2.2.1
                                      have p12985_3 := h12985c.2.2.2
                                      linarith only [hlam, p12985_0]
                                  · linarith only [h11844, h11849, h12880, hlam, p12821_1, u0elo1]
                                  · linarith only [h11844, h12880, hlam, p12821_1, u0elo1]
                            · linarith only [h11848, h12875, hlam]
                          · linarith only [h11846, h12874, hlam]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11849, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11845, hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11847, hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11849, hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11849, h12812, h12814, hc01, hc13, hlam, hphi, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11846, hlam, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11848, hlam, p12821_0]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [h11849, h12812, h12814, h9935, hc01, hc13, hlam, hphi, p12821_1]
                      · have p12821_0 := h12821c.1
                        have p12821_1 := h12821c.2.1
                        have p12821_2 := h12821c.2.2.1
                        have p12821_3 := h12821c.2.2.2
                        linarith only [hlam, p12821_0]
                · linarith only [h11844, h11848, h12815, h12816, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13103 | h13103
                · linarith only [h11847, h11849, h12809, h12812, h12814, h12815, h13103, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13105 | h13105
                  · linarith only [h11845, h11849, h13105, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13107 | h13107
                    · linarith only [h11847, h11849, h13107, hlam]
                    · rcases h0bigk with h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c | h13109c
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h0, hlam, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h6310, hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h9935, hlam, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11282, hlam, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        rcases p13109_3 (m.d 0 1) (by simp) with h13115 | h13115
                        · linarith only [h0, h13115, hlam]
                        · rcases p13109_3 (m.d 0 2) (by simp) with h13117 | h13117
                          · rcases p13109_3 (m.d 0 3) (by simp) with h13118 | h13118
                            · linarith only [h11844, h13118, hlam]
                            · linarith only [h13118, h6310, hlam]
                          · linarith only [h0, h13117, hlam]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11847, h12815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13109_1, u0elo1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11847, h12815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13109_1, u0elo1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11847, h11849, h12815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13109_1, u0elo1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        rcases p13109_3 (m.d 0 1) (by simp) with h13126 | h13126
                        · linarith only [h13126, h6310, hlam]
                        · rcases p13109_3 (m.d 0 2) (by simp) with h13128 | h13128
                          · rcases p13109_3 (m.d 0 3) (by simp) with h13129 | h13129
                            · rcases p13109_3 (m.d 0 4) (by simp) with h13130 | h13130
                              · linarith only [h11847, h13130, hlam]
                              · linarith only [h13130, h9935, hlam]
                            · linarith only [h13129, h6310, hlam]
                          · linarith only [h0, h13128, hlam]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11844, hlam, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11844, h11847, h12815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13109_1, u0elo1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11844, h11847, h11849, h12815, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13109_1, u0elo1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11849, h12809, h12812, h12814, hc01, hc12, hlam, hphi, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11845, hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11847, hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11849, hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11849, h12809, h12812, h12814, hc01, hc12, hlam, hphi, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11846, hlam, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11848, hlam, p13109_0]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [h11847, h11849, h12809, h12812, h12814, h12815, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13109_1]
                      · have p13109_0 := h13109c.1
                        have p13109_1 := h13109c.2.1
                        have p13109_2 := h13109c.2.2.1
                        have p13109_3 := h13109c.2.2.2
                        linarith only [hlam, p13109_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13149 | h13149
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13150 | h13150
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13151 | h13151
                  · linarith only [h11845, h12814, h13151, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13153 | h13153
                    · linarith only [h11844, h12814, h13149, h13153, h9935, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases h0bigk with h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c | h13155c
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h0, hlam, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h6310, hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h9935, hlam, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11282, hlam, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13161 | h13161
                        · linarith only [h0, h13161, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13163 | h13163
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13164 | h13164
                            · linarith only [h11844, h13164, hlam]
                            · linarith only [h13164, h6310, hlam]
                          · linarith only [h0, h13163, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11844, h13150, h13153, hc34, hlam, hphi, ht0b, ht45, ht5b, p13155_1, u0elo1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13170 | h13170
                        · linarith only [h0, h13170, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13172 | h13172
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13173 | h13173
                            · linarith only [h11844, h13173, hlam]
                            · linarith only [h11847, h13173, hlam]
                          · linarith only [h11845, h13172, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13177 | h13177
                        · linarith only [h0, h13177, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13179 | h13179
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13180 | h13180
                            · linarith only [h11844, h13180, hlam]
                            · linarith only [h11848, h13180, hlam]
                          · linarith only [h11846, h13179, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13184 | h13184
                        · linarith only [h13184, h6310, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13186 | h13186
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13187 | h13187
                            · rcases p13155_3 (m.d 0 4) (by simp) with h13188 | h13188
                              · linarith only [h11847, h13188, hlam]
                              · linarith only [h13188, h9935, hlam]
                            · linarith only [h13187, h6310, hlam]
                          · linarith only [h0, h13186, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11844, hlam, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13195 | h13195
                        · linarith only [h13195, h6310, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13197 | h13197
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13198 | h13198
                            · rcases p13155_3 (m.d 0 4) (by simp) with h13199 | h13199
                              · linarith only [h11847, h13199, hlam]
                              · rcases p13155_3 (m.d 0 5) (by simp) with h13201 | h13201
                                · linarith only [h11848, h13201, hlam]
                                · linarith only [h11849, h13201, hlam]
                            · linarith only [h11847, h13198, hlam]
                          · linarith only [h11845, h13197, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13206 | h13206
                        · linarith only [h13206, h6310, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13208 | h13208
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13209 | h13209
                            · rcases p13155_3 (m.d 0 4) (by simp) with h13210 | h13210
                              · linarith only [h11847, h13210, hlam]
                              · rcases p13155_3 (m.d 0 5) (by simp) with h13212 | h13212
                                · linarith only [h11848, h13212, hlam]
                                · rcases h0emin with h13214 | h13214 | h13214 | h13214 | h13214
                                  · linarith only [h12814, h13214, h9935, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · rcases h1bigk with h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c | h13216c
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h0, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h6310, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h9935, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h11282, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      rcases p13216_3 (m.d 0 1) (by simp) with h13222 | h13222
                                      · linarith only [h13222, hlam, p13216_0]
                                      · rcases p13216_3 (m.d 1 2) (by simp) with h13224 | h13224
                                        · rcases p13216_3 (m.d 1 3) (by simp) with h13225 | h13225
                                          · linarith only [h12809, h13225, hlam]
                                          · linarith only [h13225, h6310, hlam]
                                        · linarith only [h13224, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12814, h9935, hc01, hc12, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      rcases p13216_3 (m.d 0 1) (by simp) with h13233 | h13233
                                      · linarith only [h13233, hlam, p13216_0]
                                      · rcases p13216_3 (m.d 1 2) (by simp) with h13235 | h13235
                                        · rcases p13216_3 (m.d 1 3) (by simp) with h13236 | h13236
                                          · rcases p13216_3 (m.d 1 4) (by simp) with h13237 | h13237
                                            · linarith only [h12812, h13237, hlam]
                                            · linarith only [h13237, h9935, hlam]
                                          · linarith only [h13236, hlam, p13216_0]
                                        · linarith only [h0, h13235, hlam]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12809, hlam, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h9935, hc01, hc13, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12809, h12814, h9935, hc01, hc12, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12814, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12810, hlam, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12812, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12814, hlam, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      rcases p13216_3 (m.d 0 1) (by simp) with h13251 | h13251
                                      · linarith only [h13251, hlam, p13216_0]
                                      · rcases p13216_3 (m.d 1 2) (by simp) with h13253 | h13253
                                        · rcases p13216_3 (m.d 1 3) (by simp) with h13254 | h13254
                                          · rcases p13216_3 (m.d 1 4) (by simp) with h13255 | h13255
                                            · linarith only [h12814, h13255, hlam]
                                            · linarith only [h13255, h9935, hlam]
                                          · linarith only [h13254, h6310, hlam]
                                        · linarith only [h0, h13253, hlam]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12811, hlam, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h12813, hlam, p13216_0]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p13216_1]
                                    · have p13216_0 := h13216c.1
                                      have p13216_1 := h13216c.2.1
                                      have p13216_2 := h13216c.2.2.1
                                      have p13216_3 := h13216c.2.2.2
                                      linarith only [hlam, p13216_0]
                                  · rcases h1bigk with h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c | h13264c
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h0, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h6310, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h9935, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h11282, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      rcases p13264_3 (m.d 0 1) (by simp) with h13270 | h13270
                                      · linarith only [h13270, hlam, p13264_0]
                                      · rcases p13264_3 (m.d 1 2) (by simp) with h13272 | h13272
                                        · rcases p13264_3 (m.d 1 3) (by simp) with h13273 | h13273
                                          · linarith only [h12809, h13273, hlam]
                                          · linarith only [h13273, h6310, hlam]
                                        · linarith only [h13272, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      rcases p13264_3 (m.d 0 1) (by simp) with h13281 | h13281
                                      · linarith only [h13281, hlam, p13264_0]
                                      · rcases p13264_3 (m.d 1 2) (by simp) with h13283 | h13283
                                        · rcases p13264_3 (m.d 1 3) (by simp) with h13284 | h13284
                                          · rcases p13264_3 (m.d 1 4) (by simp) with h13285 | h13285
                                            · linarith only [h12812, h13285, hlam]
                                            · linarith only [h13285, h9935, hlam]
                                          · linarith only [h13284, hlam, p13264_0]
                                        · linarith only [h0, h13283, hlam]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12809, hlam, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h9935, hc01, hc13, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12809, h12814, h9935, hc01, hc12, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12814, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12810, hlam, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12812, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12814, hlam, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      rcases p13264_3 (m.d 0 1) (by simp) with h13299 | h13299
                                      · linarith only [h13299, hlam, p13264_0]
                                      · rcases p13264_3 (m.d 1 2) (by simp) with h13301 | h13301
                                        · rcases p13264_3 (m.d 1 3) (by simp) with h13302 | h13302
                                          · rcases p13264_3 (m.d 1 4) (by simp) with h13303 | h13303
                                            · linarith only [h12814, h13303, hlam]
                                            · linarith only [h13303, h9935, hlam]
                                          · linarith only [h13302, h6310, hlam]
                                        · linarith only [h0, h13301, hlam]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12811, hlam, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h12813, hlam, p13264_0]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p13264_1]
                                    · have p13264_0 := h13264c.1
                                      have p13264_1 := h13264c.2.1
                                      have p13264_2 := h13264c.2.2.1
                                      have p13264_3 := h13264c.2.2.2
                                      linarith only [hlam, p13264_0]
                                  · linarith only [h11844, h11849, h13214, hlam, p13155_1, u0elo1]
                                  · linarith only [h11844, h13214, hlam, p13155_1, u0elo1]
                            · linarith only [h11848, h13209, hlam]
                          · linarith only [h11846, h13208, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11849, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11845, hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11847, hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11849, hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13321 | h13321
                        · linarith only [h11282, h13321, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13323 | h13323
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13324 | h13324
                            · rcases p13155_3 (m.d 0 4) (by simp) with h13325 | h13325
                              · linarith only [h11849, h13325, hlam]
                              · linarith only [h13325, h9935, hlam]
                            · linarith only [h13324, h6310, hlam]
                          · linarith only [h0, h13323, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11846, hlam, p13155_1]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [h11848, hlam, p13155_0]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        rcases p13155_3 (m.d 0 1) (by simp) with h13332 | h13332
                        · linarith only [h11282, h13332, hlam]
                        · rcases p13155_3 (m.d 0 2) (by simp) with h13334 | h13334
                          · rcases p13155_3 (m.d 0 3) (by simp) with h13335 | h13335
                            · rcases p13155_3 (m.d 0 4) (by simp) with h13336 | h13336
                              · linarith only [h11849, h13336, hlam]
                              · rcases p13155_3 (m.d 0 5) (by simp) with h13338 | h13338
                                · rcases h0emin with h13339 | h13339 | h13339 | h13339 | h13339
                                  · linarith only [h12814, h13339, h9935, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · rcases h1bigk with h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c | h13341c
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h0, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h6310, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h9935, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h11282, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      rcases p13341_3 (m.d 0 1) (by simp) with h13347 | h13347
                                      · linarith only [h13347, hlam, p13341_0]
                                      · rcases p13341_3 (m.d 1 2) (by simp) with h13349 | h13349
                                        · rcases p13341_3 (m.d 1 3) (by simp) with h13350 | h13350
                                          · linarith only [h12809, h13350, hlam]
                                          · linarith only [h13350, h6310, hlam]
                                        · linarith only [h13349, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      rcases p13341_3 (m.d 0 1) (by simp) with h13358 | h13358
                                      · linarith only [h13358, hlam, p13341_0]
                                      · rcases p13341_3 (m.d 1 2) (by simp) with h13360 | h13360
                                        · rcases p13341_3 (m.d 1 3) (by simp) with h13361 | h13361
                                          · rcases p13341_3 (m.d 1 4) (by simp) with h13362 | h13362
                                            · linarith only [h12812, h13362, hlam]
                                            · linarith only [h13362, h9935, hlam]
                                          · linarith only [h13361, hlam, p13341_0]
                                        · linarith only [h0, h13360, hlam]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12809, hlam, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h9935, hc01, hc13, hlam, hphi, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h11282, h12809, h9935, hc01, hc12, hlam, hphi, p13155_1, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12814, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12810, hlam, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12812, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12814, hlam, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      rcases p13341_3 (m.d 0 1) (by simp) with h13376 | h13376
                                      · linarith only [h13376, hlam, p13341_0]
                                      · rcases p13341_3 (m.d 1 2) (by simp) with h13378 | h13378
                                        · rcases p13341_3 (m.d 1 3) (by simp) with h13379 | h13379
                                          · rcases p13341_3 (m.d 1 4) (by simp) with h13380 | h13380
                                            · linarith only [h12814, h13380, hlam]
                                            · linarith only [h13380, h9935, hlam]
                                          · linarith only [h13379, h6310, hlam]
                                        · linarith only [h0, h13378, hlam]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12811, hlam, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h12813, hlam, p13341_0]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p13341_1]
                                    · have p13341_0 := h13341c.1
                                      have p13341_1 := h13341c.2.1
                                      have p13341_2 := h13341c.2.2.1
                                      have p13341_3 := h13341c.2.2.2
                                      linarith only [hlam, p13341_0]
                                  · rcases h1bigk with h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c | h13389c
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h0, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h6310, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h9935, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h11282, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      rcases p13389_3 (m.d 0 1) (by simp) with h13395 | h13395
                                      · linarith only [h13395, hlam, p13389_0]
                                      · rcases p13389_3 (m.d 1 2) (by simp) with h13397 | h13397
                                        · rcases p13389_3 (m.d 1 3) (by simp) with h13398 | h13398
                                          · linarith only [h12809, h13398, hlam]
                                          · linarith only [h13398, h6310, hlam]
                                        · linarith only [h13397, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      rcases p13389_3 (m.d 0 1) (by simp) with h13406 | h13406
                                      · linarith only [h13406, hlam, p13389_0]
                                      · rcases p13389_3 (m.d 1 2) (by simp) with h13408 | h13408
                                        · rcases p13389_3 (m.d 1 3) (by simp) with h13409 | h13409
                                          · rcases p13389_3 (m.d 1 4) (by simp) with h13410 | h13410
                                            · linarith only [h12812, h13410, hlam]
                                            · linarith only [h13410, h9935, hlam]
                                          · linarith only [h13409, hlam, p13389_0]
                                        · linarith only [h0, h13408, hlam]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12809, hlam, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h9935, hc01, hc13, hlam, hphi, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h11282, h12809, h9935, hc01, hc12, hlam, hphi, p13155_1, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12814, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12810, hlam, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12812, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12814, hlam, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      rcases p13389_3 (m.d 0 1) (by simp) with h13424 | h13424
                                      · linarith only [h13424, hlam, p13389_0]
                                      · rcases p13389_3 (m.d 1 2) (by simp) with h13426 | h13426
                                        · rcases p13389_3 (m.d 1 3) (by simp) with h13427 | h13427
                                          · rcases p13389_3 (m.d 1 4) (by simp) with h13428 | h13428
                                            · linarith only [h12814, h13428, hlam]
                                            · linarith only [h13428, h9935, hlam]
                                          · linarith only [h13427, h6310, hlam]
                                        · linarith only [h0, h13426, hlam]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12811, hlam, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h12813, hlam, p13389_0]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p13389_1]
                                    · have p13389_0 := h13389c.1
                                      have p13389_1 := h13389c.2.1
                                      have p13389_2 := h13389c.2.2.1
                                      have p13389_3 := h13389c.2.2.2
                                      linarith only [hlam, p13389_0]
                                  · linarith only [h11844, h11848, h13339, hlam, p13155_1, u0elo1]
                                  · rcases h1bigk with h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c | h13438c
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h0, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h6310, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h9935, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h11282, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      rcases p13438_3 (m.d 0 1) (by simp) with h13444 | h13444
                                      · linarith only [h13444, hlam, p13438_0]
                                      · rcases p13438_3 (m.d 1 2) (by simp) with h13446 | h13446
                                        · rcases p13438_3 (m.d 1 3) (by simp) with h13447 | h13447
                                          · linarith only [h12809, h13447, hlam]
                                          · linarith only [h13447, h6310, hlam]
                                        · linarith only [h13446, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h6310, hc01, hc12, hlam, hphi, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h9935, hc01, hc12, hlam, hphi, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h11282, hc01, hc12, hlam, hphi, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      rcases p13438_3 (m.d 0 1) (by simp) with h13455 | h13455
                                      · linarith only [h13455, hlam, p13438_0]
                                      · rcases p13438_3 (m.d 1 2) (by simp) with h13457 | h13457
                                        · rcases p13438_3 (m.d 1 3) (by simp) with h13458 | h13458
                                          · rcases p13438_3 (m.d 1 4) (by simp) with h13459 | h13459
                                            · linarith only [h12812, h13459, hlam]
                                            · linarith only [h13459, h9935, hlam]
                                          · linarith only [h13458, hlam, p13438_0]
                                        · linarith only [h0, h13457, hlam]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12809, hlam, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h9935, hc01, hc13, hlam, hphi, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h11282, h12809, h9935, hc01, hc12, hlam, hphi, p13155_1, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12814, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12810, hlam, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12812, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12814, hlam, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      rcases p13438_3 (m.d 0 1) (by simp) with h13473 | h13473
                                      · linarith only [h13473, hlam, p13438_0]
                                      · rcases p13438_3 (m.d 1 2) (by simp) with h13475 | h13475
                                        · rcases p13438_3 (m.d 1 3) (by simp) with h13476 | h13476
                                          · rcases p13438_3 (m.d 1 4) (by simp) with h13477 | h13477
                                            · linarith only [h12814, h13477, hlam]
                                            · linarith only [h13477, h9935, hlam]
                                          · linarith only [h13476, h6310, hlam]
                                        · linarith only [h0, h13475, hlam]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12811, hlam, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h12813, hlam, p13438_0]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [h9935, hc01, hc15, hlam, hphi, p13438_1]
                                    · have p13438_0 := h13438c.1
                                      have p13438_1 := h13438c.2.1
                                      have p13438_2 := h13438c.2.2.1
                                      have p13438_3 := h13438c.2.2.2
                                      linarith only [hlam, p13438_0]
                                · linarith only [h11849, h13338, hlam]
                            · linarith only [h11847, h13335, hlam]
                          · linarith only [h11845, h13334, hlam]
                      · have p13155_0 := h13155c.1
                        have p13155_1 := h13155c.2.1
                        have p13155_2 := h13155c.2.2.1
                        have p13155_3 := h13155c.2.2.2
                        linarith only [hlam, p13155_0]
                · linarith only [h11844, h11848, h13149, h13150, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13491 | h13491
                · linarith only [h11844, h11847, h13149, h13491, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13493 | h13493
                  · linarith only [h12814, h13493, h9935, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13495 | h13495
                    · linarith only [h11847, h12814, h13495, h9935, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases h0bigk with h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c | h13497c
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h0, hlam, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h6310, hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h9935, hlam, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11282, hlam, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        rcases p13497_3 (m.d 0 1) (by simp) with h13503 | h13503
                        · linarith only [h0, h13503, hlam]
                        · rcases p13497_3 (m.d 0 2) (by simp) with h13505 | h13505
                          · rcases p13497_3 (m.d 0 3) (by simp) with h13506 | h13506
                            · linarith only [h11844, h13506, hlam]
                            · linarith only [h13506, h6310, hlam]
                          · linarith only [h0, h13505, hlam]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11847, h13149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11847, h13149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11848, h13149, h13495, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        rcases p13497_3 (m.d 0 1) (by simp) with h13514 | h13514
                        · linarith only [h13514, h6310, hlam]
                        · rcases p13497_3 (m.d 0 2) (by simp) with h13516 | h13516
                          · rcases p13497_3 (m.d 0 3) (by simp) with h13517 | h13517
                            · rcases p13497_3 (m.d 0 4) (by simp) with h13518 | h13518
                              · linarith only [h11847, h13518, hlam]
                              · linarith only [h13518, h9935, hlam]
                            · linarith only [h13517, h6310, hlam]
                          · linarith only [h0, h13516, hlam]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11844, hlam, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11847, h13149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo2]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11844, h11848, h13149, h13495, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h12814, h9935, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11845, hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11847, hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11849, hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        rcases p13497_3 (m.d 0 1) (by simp) with h13532 | h13532
                        · linarith only [h11282, h13532, hlam]
                        · rcases p13497_3 (m.d 0 2) (by simp) with h13534 | h13534
                          · rcases p13497_3 (m.d 0 3) (by simp) with h13535 | h13535
                            · rcases p13497_3 (m.d 0 4) (by simp) with h13536 | h13536
                              · linarith only [h11849, h13536, hlam]
                              · linarith only [h13536, h9935, hlam]
                            · linarith only [h13535, h6310, hlam]
                          · linarith only [h0, h13534, hlam]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11846, hlam, p13497_1]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11848, hlam, p13497_0]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [h11847, h13149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13497_1, u0elo4]
                      · have p13497_0 := h13497c.1
                        have p13497_1 := h13497c.2.1
                        have p13497_2 := h13497c.2.2.1
                        have p13497_3 := h13497c.2.2.2
                        linarith only [hlam, p13497_0]
          · linarith only [h11848, h12813, h6310, hlam]
        · linarith only [h11847, h12812, h6310, hlam]
      · linarith only [h0, h11846, h12811, hlam]
    · linarith only [h0, h11845, h12810, hlam]
  · linarith only [h0, h11844, h12809, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6310 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg9935 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg11282 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg11844 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg11845 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg11846 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h11847 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h11848 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h6310 := hg6310
  have h9935 := hg9935
  have h11282 := hg11282
  have h11844 := hg11844
  have h11845 := hg11845
  have h11846 := hg11846
  rcases m.htr 0 4 5 (by decide) (by decide) with h11849 | h11849
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s19_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg6310 hg9935 hg11282 hg11844 hg11845 hg11846 h11847 h11848 h11849

end R2N4
