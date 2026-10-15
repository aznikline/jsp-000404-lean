import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S25
import Jsp000404.R1LeavesN7_3S39
import Jsp000404.R1LeavesN7_3S41

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14801 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h15836 | h15836
  · rcases m.htr 0 2 4 (by decide) (by decide) with h15837 | h15837
    · rcases m.htr 0 2 5 (by decide) (by decide) with h15838 | h15838
      · rcases m.htr 0 3 4 (by decide) (by decide) with h15839 | h15839
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15840 | h15840
          · linarith only [h14799, h14801, h15840, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15842 | h15842
            · linarith only [h14799, h14801, h15839, h15842, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15844 | h15844
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15845 | h15845
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15846 | h15846
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15847 | h15847
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15848 | h15848
                      · linarith only [h14799, h14801, h15840, h15846, h15848, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15850 | h15850
                        · linarith only [h14799, h14801, h15842, h15847, h15850, hlam]
                        · linarith only [h14799, h14801, h15847, h15850, hc34, hc45, hlam, hphi]
                    · linarith only [h15839, h15840, h15844, h15847, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h15838, h15846, hlam]
                · linarith only [h0, h15837, h15845, hlam]
              · linarith only [h0, h15836, h15844, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15857 | h15857
          · linarith only [h14799, h14801, h15857, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15859 | h15859
            · linarith only [h14800, h14801, h15859, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15861 | h15861
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15862 | h15862
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15863 | h15863
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15864 | h15864
                    · linarith only [h14799, h14801, h15839, h15863, h15864, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15866 | h15866
                      · linarith only [h14799, h14801, h15857, h15866, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15868 | h15868
                        · linarith only [h14800, h14801, h15859, h15866, h15868, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15870 | h15870
                          · linarith only [h14799, h15839, h15861, h15870, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h15872 | h15872
                            · linarith only [h0, h14801, h15836, h15866, h15872, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h15874 | h15874
                              · linarith only [h0, h14800, h14801, h15837, h15861, h15864, h15868, h15874, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15876 | h15876
                                · linarith only [h14800, h14801, h15861, h15864, h15868, h15876, hc23, hc34, hlam, hphi]
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
                                    linarith only [h14801, h15861, h15866, hc23, hc35, hlam, hphi, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14801, h15861, h15864, h15866, h15876, hc23, hc45, hlam, hphi, ht34, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14801, hlam, p15878_0]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    rcases p15878_3 (m.d 0 1) (by simp) with h15884 | h15884
                                    · linarith only [h15884, hlam, p15878_0]
                                    · rcases p15878_3 (m.d 1 2) (by simp) with h15886 | h15886
                                      · rcases p15878_3 (m.d 1 3) (by simp) with h15887 | h15887
                                        · linarith only [h15861, h15887, hlam]
                                        · rcases p15878_3 (m.d 1 4) (by simp) with h15889 | h15889
                                          · linarith only [h15862, h15889, hlam]
                                          · rcases p15878_3 (m.d 1 5) (by simp) with h15891 | h15891
                                            · linarith only [h15863, h15891, hlam]
                                            · linarith only [h14801, h15891, hlam]
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
                                    rcases p15878_3 (m.d 0 1) (by simp) with h15896 | h15896
                                    · linarith only [h0, h15896, hlam]
                                    · linarith only [h14799, h15896, hlam]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    rcases p15878_3 (m.d 0 1) (by simp) with h15899 | h15899
                                    · linarith only [h0, h15899, hlam]
                                    · linarith only [h14800, h15899, hlam]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14800, h14801, h15861, h15864, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14799, hlam, p15878_0]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15861, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [hlam, p15878_0]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15864, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15866, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14800, hlam, p15878_0]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15862, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14800, h14801, h15861, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [hlam, p15878_0]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15868, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h14800, h15866, h15876, hc14, hc45, hlam, hphi, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [h15863, hlam, p15878_1]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    rcases p15878_3 (m.d 0 1) (by simp) with h15915 | h15915
                                    · linarith only [h14801, h15915, hlam]
                                    · linarith only [h14799, h15915, hlam]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    rcases p15878_3 (m.d 0 1) (by simp) with h15918 | h15918
                                    · linarith only [h14801, h15918, hlam]
                                    · linarith only [h14800, h15918, hlam]
                                  · have p15878_0 := h15878c.1
                                    have p15878_1 := h15878c.2.1
                                    have p15878_2 := h15878c.2.2.1
                                    have p15878_3 := h15878c.2.2.2
                                    linarith only [hlam, p15878_0]
                  · linarith only [h0, h15838, h15863, hlam]
                · linarith only [h0, h15837, h15862, hlam]
              · linarith only [h0, h15836, h15861, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h15925 | h15925
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15926 | h15926
          · linarith only [h0, h14799, h15838, h15926, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15928 | h15928
            · linarith only [h0, h14800, h15838, h15928, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15930 | h15930
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15931 | h15931
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15932 | h15932
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15933 | h15933
                    · linarith only [h0, h14799, h15838, h15932, h15933, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14799, h15838, h15925, h15932, h15933, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15936 | h15936
                    · linarith only [h0, h14799, h15932, h15936, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h14799, h15925, h15930, h15932, h15936, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h14799, h15837, h15838, h15925, h15931, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h15836, h15930, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h15941 | h15941
          · linarith only [h14799, h14801, h15941, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h15943 | h15943
            · linarith only [h0, h14800, h15838, h15943, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15945 | h15945
              · rcases m.htr 1 2 4 (by decide) (by decide) with h15946 | h15946
                · rcases m.htr 1 2 5 (by decide) (by decide) with h15947 | h15947
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h15948 | h15948
                    · linarith only [h0, h14799, h15838, h15925, h15947, h15948, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15950 | h15950
                      · linarith only [h0, h14799, h15838, h15941, h15950, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h15952 | h15952
                        · linarith only [h0, h14800, h15838, h15943, h15947, h15952, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h15954 | h15954
                          · linarith only [h14799, h15925, h15945, h15954, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h15956 | h15956
                            · linarith only [h0, h14800, h15838, h15945, h15947, h15948, h15956, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h15958 | h15958
                              · linarith only [h0, h14800, h15838, h15946, h15947, h15952, h15958, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h15960 | h15960
                                · linarith only [h0, h14800, h15838, h15945, h15947, h15948, h15952, h15960, hc23, hc34, hlam, hphi]
                                · rcases h1bigk with h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c | h15962c
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h15838, h15945, h15947, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h15838, h15947, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h14801, hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    rcases p15962_3 (m.d 0 1) (by simp) with h15968 | h15968
                                    · linarith only [h15968, hlam, p15962_0]
                                    · rcases p15962_3 (m.d 1 2) (by simp) with h15970 | h15970
                                      · rcases p15962_3 (m.d 1 3) (by simp) with h15971 | h15971
                                        · linarith only [h15945, h15971, hlam]
                                        · rcases p15962_3 (m.d 1 4) (by simp) with h15973 | h15973
                                          · linarith only [h15946, h15973, hlam]
                                          · rcases p15962_3 (m.d 1 5) (by simp) with h15975 | h15975
                                            · linarith only [h15947, h15975, hlam]
                                            · linarith only [h14801, h15975, hlam]
                                      · linarith only [h15970, hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h14799, h15838, h15947, hlam, p15962_2]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h14800, h15838, h15947, hlam, p15962_2]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h15838, h15947, hc01, hc12, hlam, hphi, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h14799, hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15945, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15948, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15950, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h14800, hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15946, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h0, h14800, h15838, h15947, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [hlam, p15962_0]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15952, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h14799, h15950, hc13, hc35, hlam, hphi, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [h15947, hlam, p15962_1]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    rcases p15962_3 (m.d 0 1) (by simp) with h15995 | h15995
                                    · linarith only [h14801, h15995, hlam]
                                    · linarith only [h14799, h15995, hlam]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    rcases p15962_3 (m.d 0 1) (by simp) with h15998 | h15998
                                    · linarith only [h14801, h15998, hlam]
                                    · linarith only [h14800, h15998, hlam]
                                  · have p15962_0 := h15962c.1
                                    have p15962_1 := h15962c.2.1
                                    have p15962_2 := h15962c.2.2.1
                                    have p15962_3 := h15962c.2.2.2
                                    linarith only [hlam, p15962_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h16002 | h16002
                    · linarith only [h0, h14799, h15947, h16002, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h16004 | h16004
                      · linarith only [h0, h14800, h15947, h16002, h16004, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h16006 | h16006
                        · linarith only [h0, h14800, h15947, h16006, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h16008 | h16008
                          · linarith only [h14799, h15925, h15945, h16008, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h16010 | h16010
                            · linarith only [h0, h14800, h15945, h15947, h16002, h16010, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h14800, h15947, h16002, h16010, hc13, hc35, hlam, hphi]
                · linarith only [h0, h14799, h15837, h15945, h15946, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h15836, h15945, hlam]
    · linarith only [h0, h14800, h15837, hlam]
  · linarith only [h0, h14799, h15836, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h14801 | h14801
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800 h14801
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800 h14801

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14800 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h16017 | h16017
  · rcases m.htr 0 2 3 (by decide) (by decide) with h16018 | h16018
    · rcases m.htr 0 2 4 (by decide) (by decide) with h16019 | h16019
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16020 | h16020
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16021 | h16021
          · linarith only [h14799, h14800, h16021, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16023 | h16023
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16024 | h16024
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16025 | h16025
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16026 | h16026
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16027 | h16027
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16028 | h16028
                      · linarith only [h14799, h14800, h16021, h16026, h16028, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16030 | h16030
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16031 | h16031
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16032 | h16032
                            · linarith only [h14799, h14800, h16028, h16030, h16032, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16034 | h16034
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16035 | h16035
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16036 | h16036
                                  · rcases h1bigk with h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c | h16037c
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h0, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14800, h16025, h16026, h16034, h16036, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14800, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      rcases p16037_3 (m.d 0 1) (by simp) with h16042 | h16042
                                      · rcases p16037_3 (m.d 1 2) (by simp) with h16043 | h16043
                                        · rcases p16037_3 (m.d 1 3) (by simp) with h16044 | h16044
                                          · linarith only [h14799, h16044, hlam]
                                          · linarith only [h16030, h16044, hlam]
                                        · linarith only [h16027, h16043, hlam]
                                      · linarith only [h16042, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14799, h16025, h16034, h16036, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      rcases p16037_3 (m.d 0 1) (by simp) with h16051 | h16051
                                      · linarith only [h0, h16051, hlam]
                                      · linarith only [h14799, h16051, hlam]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14799, h14800, h16025, h16034, h16036, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      rcases p16037_3 (m.d 0 1) (by simp) with h16055 | h16055
                                      · linarith only [h0, h16055, hlam]
                                      · linarith only [h16017, h16055, hlam]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14799, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16025, hlam, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16028, hlam, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14799, h14800, h16026, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h14799, h16025, h16026, h16034, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16026, hlam, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      rcases p16037_3 (m.d 0 1) (by simp) with h16065 | h16065
                                      · linarith only [h14800, h16065, hlam]
                                      · linarith only [h14799, h16065, hlam]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      rcases p16037_3 (m.d 0 1) (by simp) with h16069 | h16069
                                      · linarith only [h14800, h16069, hlam]
                                      · linarith only [h16017, h16069, hlam]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16017, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16027, hlam, p16037_1]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16030, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [h16031, hlam, p16037_0]
                                    · have p16037_0 := h16037c.1
                                      have p16037_1 := h16037c.2.1
                                      have p16037_2 := h16037c.2.2.1
                                      have p16037_3 := h16037c.2.2.2
                                      linarith only [hlam, p16037_0]
                                  · linarith only [h16021, h16024, h16036, hlam]
                                · linarith only [h0, h14799, h16030, h16031, h16032, h16034, h16035, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h14799, h14800, h16023, h16028, h16034, hc23, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16031, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h14799, h14800, h16023, h16028, h16030, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h16020, h16027, hlam]
                  · linarith only [h0, h16019, h16026, hlam]
                · linarith only [h0, h16018, h16025, hlam]
              · linarith only [h14799, h14800, h16023, h16024, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16086 | h16086
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16087 | h16087
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16088 | h16088
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16089 | h16089
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16090 | h16090
                      · linarith only [h14799, h14800, h16021, h16088, h16090, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16092 | h16092
                        · linarith only [h14799, h16023, h16092, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16094 | h16094
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16095 | h16095
                            · linarith only [h0, h14800, h16018, h16090, h16095, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16097 | h16097
                              · linarith only [h14799, h16023, h16087, h16097, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16099 | h16099
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16100 | h16100
                                  · rcases h1bigk with h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c | h16101c
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h0, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h14800, h16087, h16090, hc23, hc34, hlam, hphi, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h14800, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h14800, h16087, h16090, h16092, hc23, hc34, hlam, hphi, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      rcases p16101_3 (m.d 0 1) (by simp) with h16107 | h16107
                                      · linarith only [h16107, hlam, p16101_0]
                                      · rcases p16101_3 (m.d 1 2) (by simp) with h16109 | h16109
                                        · rcases p16101_3 (m.d 1 3) (by simp) with h16110 | h16110
                                          · linarith only [h16087, h16110, hlam]
                                          · rcases p16101_3 (m.d 1 4) (by simp) with h16112 | h16112
                                            · linarith only [h16088, h16112, hlam]
                                            · linarith only [h14800, h16112, hlam]
                                        · linarith only [h16109, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      rcases p16101_3 (m.d 0 1) (by simp) with h16117 | h16117
                                      · linarith only [h0, h16117, hlam]
                                      · linarith only [h14799, h16117, hlam]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h14800, h16017, h16087, h16092, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      rcases p16101_3 (m.d 0 1) (by simp) with h16121 | h16121
                                      · linarith only [h0, h16121, hlam]
                                      · linarith only [h16017, h16121, hlam]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h14799, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16087, hlam, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16090, hlam, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16092, hlam, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16017, h16087, h16090, h16092, hc23, hc34, hlam, hphi, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16088, hlam, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      rcases p16101_3 (m.d 0 1) (by simp) with h16131 | h16131
                                      · linarith only [h14800, h16131, hlam]
                                      · linarith only [h14799, h16131, hlam]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      rcases p16101_3 (m.d 0 1) (by simp) with h16135 | h16135
                                      · linarith only [h14800, h16135, hlam]
                                      · linarith only [h16017, h16135, hlam]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16017, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16089, hlam, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h0, h16017, h16087, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16101_1]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [h16094, hlam, p16101_0]
                                    · have p16101_0 := h16101c.1
                                      have p16101_1 := h16101c.2.1
                                      have p16101_2 := h16101c.2.2.1
                                      have p16101_3 := h16101c.2.2.2
                                      linarith only [hlam, p16101_0]
                                  · linarith only [h14799, h14800, h16087, h16090, h16100, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h14800, h16017, h16090, h16094, h16095, h16099, hc23, hc34, hlam, hphi]
                          · linarith only [h14800, h16017, h16092, h16094, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16020, h16089, hlam]
                  · linarith only [h0, h16019, h16088, hlam]
                · linarith only [h0, h16018, h16087, hlam]
              · linarith only [h14800, h16017, h16086, hlam]
        · linarith only [h0, h16017, h16020, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16151 | h16151
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16152 | h16152
          · linarith only [h0, h14799, h16019, h16152, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16154 | h16154
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16155 | h16155
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16156 | h16156
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16157 | h16157
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16158 | h16158
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16159 | h16159
                      · linarith only [h0, h14799, h16019, h16152, h16157, h16159, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16161 | h16161
                        · linarith only [h0, h14799, h16019, h16157, h16161, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h14799, h16019, h16154, h16156, h16157, h16161, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h16019, h16157, h16158, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16165 | h16165
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16166 | h16166
                      · linarith only [h0, h14799, h16019, h16152, h16157, h16166, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16168 | h16168
                        · linarith only [h0, h14799, h16157, h16168, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h14799, h16154, h16156, h16157, h16168, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h16017, h16019, h16151, h16165, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h16018, h16156, hlam]
              · linarith only [h0, h14799, h16019, h16154, h16155, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16174 | h16174
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16175 | h16175
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16176 | h16176
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16177 | h16177
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16178 | h16178
                      · linarith only [h0, h14799, h16019, h16152, h16176, h16178, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16180 | h16180
                        · linarith only [h0, h14799, h16019, h16154, h16176, h16180, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16182 | h16182
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16183 | h16183
                            · linarith only [h14800, h16018, h16019, h16176, h16178, h16183, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16185 | h16185
                              · linarith only [h14799, h16154, h16175, h16185, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16187 | h16187
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16188 | h16188
                                  · rcases h1bigk with h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c | h16189c
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h16019, h16175, h16176, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h14800, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h16019, h16175, h16176, h16180, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      rcases p16189_3 (m.d 0 1) (by simp) with h16195 | h16195
                                      · linarith only [h16195, hlam, p16189_0]
                                      · rcases p16189_3 (m.d 1 2) (by simp) with h16197 | h16197
                                        · rcases p16189_3 (m.d 1 3) (by simp) with h16198 | h16198
                                          · linarith only [h16175, h16198, hlam]
                                          · rcases p16189_3 (m.d 1 4) (by simp) with h16200 | h16200
                                            · linarith only [h16176, h16200, hlam]
                                            · linarith only [h14800, h16200, hlam]
                                        · linarith only [h16197, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h14799, h16019, h16176, hlam, p16189_2]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h16019, h16176, hc01, hc12, hlam, hphi, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h16017, h16019, h16176, hlam, p16189_2]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h14799, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16175, hlam, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16178, hlam, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16180, hlam, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16017, h16175, h16178, h16180, hc23, hc34, hlam, hphi, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16176, hlam, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      rcases p16189_3 (m.d 0 1) (by simp) with h16215 | h16215
                                      · linarith only [h14800, h16215, hlam]
                                      · linarith only [h14799, h16215, hlam]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      rcases p16189_3 (m.d 0 1) (by simp) with h16219 | h16219
                                      · linarith only [h14800, h16219, hlam]
                                      · linarith only [h16017, h16219, hlam]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16017, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16177, hlam, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h0, h16017, h16019, h16175, h16176, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16189_1]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [h16182, hlam, p16189_0]
                                    · have p16189_0 := h16189c.1
                                      have p16189_1 := h16189c.2.1
                                      have p16189_2 := h16189c.2.2.1
                                      have p16189_3 := h16189c.2.2.2
                                      linarith only [hlam, p16189_0]
                                  · linarith only [h14799, h14800, h16175, h16178, h16188, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h16017, h16019, h16182, h16187, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h16017, h16019, h16175, h16176, h16180, h16182, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16019, h16176, h16177, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16231 | h16231
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16232 | h16232
                      · linarith only [h0, h14799, h16176, h16232, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16234 | h16234
                        · linarith only [h14799, h16154, h16234, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16236 | h16236
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16237 | h16237
                            · linarith only [h0, h16017, h16175, h16176, h16232, h16234, h16237, hlam]
                            · linarith only [h0, h16017, h16175, h16176, h16234, h16237, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h16017, h16175, h16176, h16234, h16236, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16151, h16231, hlam]
                · linarith only [h0, h16018, h16175, hlam]
              · linarith only [h0, h16017, h16019, h16174, hlam]
        · linarith only [h0, h16017, h16151, hlam]
    · linarith only [h0, h14799, h16018, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h16246 | h16246
    · rcases m.htr 0 2 4 (by decide) (by decide) with h16247 | h16247
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16248 | h16248
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16249 | h16249
          · linarith only [h14799, h14800, h16249, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16251 | h16251
            · linarith only [h14799, h16017, h16251, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16253 | h16253
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16254 | h16254
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16255 | h16255
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16256 | h16256
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16257 | h16257
                      · linarith only [h14799, h14800, h16249, h16255, h16257, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16259 | h16259
                        · linarith only [h14799, h16017, h16251, h16259, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16261 | h16261
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16262 | h16262
                            · linarith only [h14799, h16017, h16246, h16257, h16261, h16262, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16264 | h16264
                              · linarith only [h14799, h16017, h16254, h16259, h16264, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16266 | h16266
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16267 | h16267
                                  · rcases h1bigk with h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c | h16268c
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h0, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14800, h16254, h16257, hc23, hc34, hlam, hphi, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14800, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16017, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      rcases p16268_3 (m.d 0 1) (by simp) with h16274 | h16274
                                      · linarith only [h16274, hlam, p16268_0]
                                      · rcases p16268_3 (m.d 1 2) (by simp) with h16276 | h16276
                                        · rcases p16268_3 (m.d 1 3) (by simp) with h16277 | h16277
                                          · linarith only [h16254, h16277, hlam]
                                          · rcases p16268_3 (m.d 1 4) (by simp) with h16279 | h16279
                                            · linarith only [h16255, h16279, hlam]
                                            · linarith only [h14800, h16279, hlam]
                                        · linarith only [h16276, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      rcases p16268_3 (m.d 0 1) (by simp) with h16284 | h16284
                                      · linarith only [h0, h16284, hlam]
                                      · linarith only [h14799, h16284, hlam]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14800, hc01, hc12, hlam, hphi, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14799, h16017, h16254, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14799, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16254, hlam, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16257, hlam, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16259, hlam, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14799, h16254, h16257, hc23, hc34, hlam, hphi, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16255, hlam, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      rcases p16268_3 (m.d 0 1) (by simp) with h16296 | h16296
                                      · linarith only [h14800, h16296, hlam]
                                      · linarith only [h14799, h16296, hlam]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14799, h16017, h16254, h16257, hc23, hc34, hlam, hphi, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h14799, h16254, h16259, hc23, hc35, hlam, hphi, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16256, hlam, p16268_1]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      rcases p16268_3 (m.d 0 1) (by simp) with h16303 | h16303
                                      · linarith only [h16017, h16303, hlam]
                                      · linarith only [h14799, h16303, hlam]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [h16261, hlam, p16268_0]
                                    · have p16268_0 := h16268c.1
                                      have p16268_1 := h16268c.2.1
                                      have p16268_2 := h16268c.2.2.1
                                      have p16268_3 := h16268c.2.2.2
                                      linarith only [hlam, p16268_0]
                                  · linarith only [h0, h14799, h14800, h16247, h16254, h16257, h16266, h16267, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16309 | h16309
                                  · rcases h1bigk with h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c | h16310c
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h0, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14800, h16254, h16257, hc23, hc34, hlam, hphi, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14800, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16017, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      rcases p16310_3 (m.d 0 1) (by simp) with h16316 | h16316
                                      · linarith only [h16316, hlam, p16310_0]
                                      · rcases p16310_3 (m.d 1 2) (by simp) with h16318 | h16318
                                        · rcases p16310_3 (m.d 1 3) (by simp) with h16319 | h16319
                                          · linarith only [h16254, h16319, hlam]
                                          · rcases p16310_3 (m.d 1 4) (by simp) with h16321 | h16321
                                            · linarith only [h16255, h16321, hlam]
                                            · linarith only [h14800, h16321, hlam]
                                        · linarith only [h16318, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      rcases p16310_3 (m.d 0 1) (by simp) with h16326 | h16326
                                      · linarith only [h0, h16326, hlam]
                                      · linarith only [h14799, h16326, hlam]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14800, h16253, h16266, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16017, hc01, hc12, hlam, hphi, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14799, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16254, hlam, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16257, hlam, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16259, hlam, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14799, h16254, h16257, hc23, hc34, hlam, hphi, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16255, hlam, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      rcases p16310_3 (m.d 0 1) (by simp) with h16338 | h16338
                                      · linarith only [h14800, h16338, hlam]
                                      · linarith only [h14799, h16338, hlam]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14799, h16017, h16254, h16257, hc23, hc34, hlam, hphi, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h14799, h16254, h16259, hc23, hc35, hlam, hphi, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16256, hlam, p16310_1]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      rcases p16310_3 (m.d 0 1) (by simp) with h16345 | h16345
                                      · linarith only [h16017, h16345, hlam]
                                      · linarith only [h14799, h16345, hlam]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [h16261, hlam, p16310_0]
                                    · have p16310_0 := h16310c.1
                                      have p16310_1 := h16310c.2.1
                                      have p16310_2 := h16310c.2.2.1
                                      have p16310_3 := h16310c.2.2.2
                                      linarith only [hlam, p16310_0]
                                  · linarith only [h14799, h14800, h16254, h16257, h16309, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h14800, h16253, h16261, hlam]
                    · linarith only [h0, h14799, h16248, h16254, h16256, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h16247, h16255, hlam]
                · linarith only [h0, h16246, h16254, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16355 | h16355
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16356 | h16356
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16357 | h16357
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16358 | h16358
                      · linarith only [h14799, h14800, h16253, h16358, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16360 | h16360
                        · linarith only [h14799, h16251, h16360, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16362 | h16362
                          · linarith only [h14799, h14800, h16253, h16358, h16362, hc13, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16355, h16362, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16248, h16357, hlam]
                  · linarith only [h0, h16247, h16356, hlam]
                · linarith only [h0, h14799, h16246, h16355, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16368 | h16368
          · linarith only [h14799, h14800, h16368, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16370 | h16370
            · linarith only [h14799, h16017, h16370, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16372 | h16372
              · linarith only [h16247, h16248, h16372, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16374 | h16374
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16375 | h16375
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16376 | h16376
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16377 | h16377
                      · linarith only [h0, h14799, h16368, h16377, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16379 | h16379
                        · linarith only [h14799, h14800, h16247, h16248, h16370, h16379, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16381 | h16381
                          · linarith only [h14799, h14800, h16372, h16377, h16381, hc13, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16374, h16381, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16384 | h16384
                      · linarith only [h14799, h14800, h16375, h16376, h16384, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16386 | h16386
                        · linarith only [h14799, h14800, h16375, h16376, h16386, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16388 | h16388
                          · linarith only [h14799, h14800, h16372, h16374, h16375, h16376, h16388, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h14799, h14800, h16374, h16388, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h16247, h16375, hlam]
                · linarith only [h0, h16246, h16374, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16393 | h16393
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16394 | h16394
          · linarith only [h0, h14799, h16247, h16394, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16396 | h16396
            · linarith only [h14799, h16017, h16396, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16398 | h16398
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16399 | h16399
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16400 | h16400
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16401 | h16401
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16402 | h16402
                      · linarith only [h14799, h16017, h16247, h16393, h16394, h16400, h16402, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16404 | h16404
                        · linarith only [h14799, h16017, h16396, h16404, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16406 | h16406
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16407 | h16407
                            · linarith only [h16017, h16246, h16247, h16400, h16402, h16406, h16407, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16409 | h16409
                              · linarith only [h14799, h16017, h16399, h16404, h16409, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16411 | h16411
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16412 | h16412
                                  · rcases h1bigk with h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c | h16413c
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h0, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16017, h16399, h16404, hc23, hc35, hlam, hphi, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14800, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16017, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      rcases p16413_3 (m.d 0 1) (by simp) with h16419 | h16419
                                      · linarith only [h16419, hlam, p16413_0]
                                      · rcases p16413_3 (m.d 1 2) (by simp) with h16421 | h16421
                                        · rcases p16413_3 (m.d 1 3) (by simp) with h16422 | h16422
                                          · linarith only [h16399, h16422, hlam]
                                          · rcases p16413_3 (m.d 1 4) (by simp) with h16424 | h16424
                                            · linarith only [h16400, h16424, hlam]
                                            · linarith only [h14800, h16424, hlam]
                                        · linarith only [h16421, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, h16017, h16247, h16393, h16400, hlam, p16413_2]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16017, h16247, h16393, h16400, hc01, hc12, hlam, hphi, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, h16017, h16399, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16399, hlam, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16402, hlam, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16404, hlam, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, h16399, h16402, hc23, hc34, hlam, hphi, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16400, hlam, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      rcases p16413_3 (m.d 0 1) (by simp) with h16439 | h16439
                                      · linarith only [h14800, h16439, hlam]
                                      · linarith only [h14799, h16439, hlam]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, h16017, h16399, h16402, hc23, hc34, hlam, hphi, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h14799, h16399, h16404, h16412, hc23, hc34, hlam, hphi, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16401, hlam, p16413_1]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      rcases p16413_3 (m.d 0 1) (by simp) with h16446 | h16446
                                      · linarith only [h16017, h16446, hlam]
                                      · linarith only [h14799, h16446, hlam]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [h16406, hlam, p16413_0]
                                    · have p16413_0 := h16413c.1
                                      have p16413_1 := h16413c.2.1
                                      have p16413_2 := h16413c.2.2.1
                                      have p16413_3 := h16413c.2.2.2
                                      linarith only [hlam, p16413_0]
                                  · linarith only [h14799, h14800, h16399, h16402, h16412, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h14799, h16017, h16247, h16393, h16398, h16399, h16411, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h16247, h16393, h16398, h16400, h16406, hlam]
                    · linarith only [h16247, h16393, h16401, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16455 | h16455
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16456 | h16456
                      · linarith only [h14799, h16017, h16394, h16400, h16455, h16456, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16458 | h16458
                        · linarith only [h14799, h16017, h16400, h16455, h16458, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16460 | h16460
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16461 | h16461
                            · linarith only [h14799, h16017, h16399, h16400, h16455, h16456, h16461, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h14799, h16017, h16400, h16455, h16461, hc13, hc34, hlam, hphi]
                          · linarith only [h14799, h16017, h16398, h16399, h16400, h16455, h16460, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h14799, h16393, h16399, h16455, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h16246, h16399, hlam]
              · linarith only [h16247, h16393, h16398, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16468 | h16468
          · linarith only [h0, h14799, h16247, h16468, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16470 | h16470
            · linarith only [h14799, h16017, h16470, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16472 | h16472
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16473 | h16473
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16474 | h16474
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16475 | h16475
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16476 | h16476
                      · linarith only [h0, h14799, h16247, h16468, h16474, h16476, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16478 | h16478
                        · linarith only [h0, h14799, h16393, h16470, h16478, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16480 | h16480
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16481 | h16481
                            · linarith only [h14800, h16246, h16247, h16474, h16476, h16481, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16483 | h16483
                              · linarith only [h0, h14799, h16393, h16473, h16475, h16478, h16483, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16485 | h16485
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16486 | h16486
                                  · rcases h1bigk with h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c | h16487c
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, h16393, h16474, h16485, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h14800, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16017, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      rcases p16487_3 (m.d 0 1) (by simp) with h16493 | h16493
                                      · linarith only [h16493, hlam, p16487_0]
                                      · rcases p16487_3 (m.d 1 2) (by simp) with h16495 | h16495
                                        · rcases p16487_3 (m.d 1 3) (by simp) with h16496 | h16496
                                          · linarith only [h16473, h16496, hlam]
                                          · rcases p16487_3 (m.d 1 4) (by simp) with h16498 | h16498
                                            · linarith only [h16474, h16498, hlam]
                                            · linarith only [h14800, h16498, hlam]
                                        · linarith only [h16495, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, h14799, h16393, h16474, h16485, hlam, p16487_2]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, h16393, h16475, h16480, hc01, hc12, hlam, hphi, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, h14799, h16393, h16473, h16475, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h14799, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16473, hlam, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16476, hlam, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16478, hlam, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h14799, h16473, h16476, hc23, hc34, hlam, hphi, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16474, hlam, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      rcases p16487_3 (m.d 0 1) (by simp) with h16513 | h16513
                                      · linarith only [h14800, h16513, hlam]
                                      · linarith only [h14799, h16513, hlam]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h0, h14799, h16393, h16473, h16475, h16476, hc23, hc34, hlam, hphi, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h14799, h16473, h16478, hc23, hc35, hlam, hphi, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16475, hlam, p16487_1]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      rcases p16487_3 (m.d 0 1) (by simp) with h16520 | h16520
                                      · linarith only [h16017, h16520, hlam]
                                      · linarith only [h14799, h16520, hlam]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [h16480, hlam, p16487_0]
                                    · have p16487_0 := h16487c.1
                                      have p16487_1 := h16487c.2.1
                                      have p16487_2 := h16487c.2.2.1
                                      have p16487_3 := h16487c.2.2.2
                                      linarith only [hlam, p16487_0]
                                  · linarith only [h14799, h14800, h16472, h16473, h16476, h16486, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h16247, h16472, h16485, hlam]
                          · linarith only [h14799, h14800, h16472, h16473, h16480, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h14799, h16247, h16473, h16474, h16475, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16529 | h16529
                    · linarith only [h0, h14799, h16393, h16473, h16474, h16529, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16531 | h16531
                      · linarith only [h0, h14799, h16468, h16474, h16531, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16533 | h16533
                        · linarith only [h0, h14799, h16474, h16533, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16535 | h16535
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16536 | h16536
                            · linarith only [h0, h14799, h16473, h16529, h16531, h16535, h16536, hlam]
                            · linarith only [h0, h14799, h16474, h16536, hc13, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16472, h16473, h16535, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h14799, h16246, h16473, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16541 | h16541
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16542 | h16542
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16543 | h16543
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16544 | h16544
                      · linarith only [h0, h14799, h16247, h16542, h16544, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16546 | h16546
                        · linarith only [h0, h14799, h16247, h16542, h16546, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16548 | h16548
                          · linarith only [h14799, h14800, h16472, h16544, h16548, hc13, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16541, h16548, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h14799, h16247, h16541, h16542, h16543, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16552 | h16552
                    · linarith only [h0, h14799, h16393, h16541, h16542, h16552, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16554 | h16554
                      · linarith only [h0, h14799, h16542, h16554, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16556 | h16556
                        · linarith only [h0, h14799, h16542, h16556, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16558 | h16558
                          · linarith only [h0, h14799, h16247, h16472, h16541, h16554, h16558, hc23, hc34, hlam, hphi]
                          · linarith only [h14799, h14800, h16541, h16558, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h14799, h16246, h16541, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h14799, h16246, hlam]

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h14800 | h14800
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x0 m hb1 hb3 hb5 hg0 h14799 h14800
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0_x1 m hb1 hb3 hb5 hg0 h14799 h14800

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  exact r1l7_11_13_25_L_I_L_I_H_I_s14 m hb1 hb3 hb5 h0 h14799

set_option maxHeartbeats 19638000 in
set_option maxHeartbeats 19638000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s13 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h14799 | h14799
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x0 m hb1 hb3 hb5 hg0 h14799
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13_x1 m hb1 hb3 hb5 hg0 h14799

set_option maxHeartbeats 49236000 in
set_option maxHeartbeats 49236000 in
theorem r1l7_11_13_25_L_I_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_I_H_I_s0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_I_H_I_s13 m hb1 hb3 hb5 h0

end R2N4
