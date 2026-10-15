import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3256000 in
theorem r1l7_11_13_25_L_0_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h834 | h834
  · rcases m.htr 0 1 4 (by decide) (by decide) with h835 | h835
    · rcases m.htr 0 1 5 (by decide) (by decide) with h836 | h836
      · rcases m.htr 0 2 3 (by decide) (by decide) with h837 | h837
        · rcases m.htr 0 2 5 (by decide) (by decide) with h838 | h838
          · rcases m.htr 0 3 4 (by decide) (by decide) with h839 | h839
            · rcases m.htr 0 3 5 (by decide) (by decide) with h840 | h840
              · rcases m.htr 0 4 5 (by decide) (by decide) with h841 | h841
                · rcases m.htr 1 2 3 (by decide) (by decide) with h842 | h842
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h843 | h843
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h844 | h844
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h845 | h845
                        · linarith only [h0, h834, h845, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h839, h842, h845, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h835, h838, h844, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h835, h843, hlam]
                  · linarith only [h0, h842, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h852 | h852
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h853 | h853
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h854 | h854
                        · linarith only [h0, h834, h854, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h839, h854, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h834, h838, h839, h853, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h835, h852, hlam]
                  · linarith only [h0, h851, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h860 | h860
                · linarith only [h839, h840, h860, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h862 | h862
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h863 | h863
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                        · linarith only [h0, h834, h865, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h839, h840, h862, h865, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h838, h864, hlam]
                    · linarith only [h0, h835, h863, hlam]
                  · linarith only [h0, h862, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h871 | h871
              · rcases m.htr 0 4 5 (by decide) (by decide) with h872 | h872
                · rcases m.htr 1 2 3 (by decide) (by decide) with h873 | h873
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h874 | h874
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h875 | h875
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h876 | h876
                        · linarith only [h0, h834, h839, h876, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                          · linarith only [h0, h835, h876, h878, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h839, h871, h873, h878, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h838, h875, hlam]
                    · linarith only [h0, h835, h874, hlam]
                  · linarith only [h0, h873, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h839, h871, h872, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h889 | h889
                        · linarith only [h839, h889, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                          · linarith only [h834, h871, h891, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
                            · linarith only [h0, h835, h893, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                            · linarith only [h0, h835, h885, h887, h893, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · linarith only [h0, h838, h888, hlam]
                    · linarith only [h0, h835, h887, hlam]
                  · linarith only [h0, h886, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h899 | h899
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h901 | h901
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h902 | h902
                        · linarith only [h834, h839, h902, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
                          · linarith only [h834, h871, h904, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h906 | h906
                            · linarith only [h0, h834, h835, h839, h885, h899, h906, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                              · linarith only [h834, h839, h899, h908, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                                · linarith only [h834, h871, h899, h910, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h912 | h912
                                  · linarith only [h834, h839, h885, h899, h900, h912, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                                    · linarith only [h834, h839, h885, h899, h914, hc23, hlam, hphi, u3elo3]
                                    · rcases h5bigk with h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c | h916c
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hlam, p916_0]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h0, h836, h899, h902, h906, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p916_1, u1elo1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h0, h836, hc25, hlam, hphi, ht01, ht0b, ht5b, p916_1, u1elo1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h871, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h885, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h836, hlam, p916_0]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hlam, p916_0]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p916_1, u1elo4]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h904, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h906, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h838, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h901, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hlam, p916_0]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h910, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h912, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p916_1, u3elo4]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h0, h835, h899, h901, h902, hc23, hc25, hlam, hphi, ht01, ht0b, ht5b, p916_1, u1elo1, u3elo4]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h0, h836, h899, h902, h906, hc23, hc25, hlam, hphi, ht01, ht0b, ht5b, p916_1, u1elo1, u3elo4]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hlam, p916_0]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h914, hlam, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h834, h839, h885, h899, hc23, hc45, hlam, hphi, ht34, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h899, h902, h906, hc23, hc45, hlam, hphi, ht34, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h910, hc23, hc45, hlam, hphi, ht34, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [h834, h871, h899, hc23, hc45, hlam, hphi, ht34, p916_1]
                                      · have p916_0 := h916c.1
                                        have p916_1 := h916c.2.1
                                        have p916_2 := h916c.2.2.1
                                        have p916_3 := h916c.2.2.2
                                        linarith only [hlam, p916_0]
                      · linarith only [h0, h838, h901, hlam]
                    · linarith only [h0, h835, h900, hlam]
                  · linarith only [h0, h899, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h0, h836, h838, hlam]
        · linarith only [h0, h834, h837, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h947 | h947
        · rcases m.htr 0 2 5 (by decide) (by decide) with h948 | h948
          · rcases m.htr 0 3 4 (by decide) (by decide) with h949 | h949
            · rcases m.htr 0 3 5 (by decide) (by decide) with h950 | h950
              · linarith only [h834, h836, h950, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h952 | h952
                · linarith only [h834, h836, h949, h952, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h954 | h954
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h955 | h955
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h956 | h956
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h957 | h957
                        · linarith only [h834, h836, h956, h957, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h949, h950, h957, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h948, h956, hlam]
                    · linarith only [h0, h835, h955, hlam]
                  · linarith only [h0, h954, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h963 | h963
              · linarith only [h835, h836, h949, h963, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h965 | h965
                · linarith only [h835, h836, h965, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h967 | h967
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h969 | h969
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
                        · linarith only [h834, h836, h949, h969, h970, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h972 | h972
                          · linarith only [h834, h836, h963, h972, hlam]
                          · linarith only [h835, h836, h967, h970, h972, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h835, h948, h969, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h835, h968, hlam]
                  · linarith only [h0, h967, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h978 | h978
            · rcases m.htr 0 3 5 (by decide) (by decide) with h979 | h979
              · linarith only [h0, h834, h948, h979, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h981 | h981
                · linarith only [h0, h834, h948, h978, h981, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h983 | h983
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h985 | h985
                      · linarith only [h0, h834, h948, h983, h985, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h987 | h987
                        · linarith only [h0, h834, h985, h987, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h978, h979, h987, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h835, h984, hlam]
                  · linarith only [h0, h983, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h992 | h992
              · linarith only [h0, h835, h948, h978, h992, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h994 | h994
                · linarith only [h0, h835, h948, h994, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h996 | h996
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h997 | h997
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h998 | h998
                      · linarith only [h0, h834, h948, h996, h998, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1000 | h1000
                        · linarith only [h1000, h834, h978, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1002 | h1002
                          · linarith only [h0, h1002, h834, h948, h992, hlam]
                          · linarith only [h1000, h1002, h835, h836, h996, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h835, h997, hlam]
                  · linarith only [h0, h996, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h0, h834, h947, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1008 | h1008
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1009 | h1009
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1010 | h1010
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1011 | h1011
            · linarith only [h1011, h834, h835, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1013 | h1013
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1014 | h1014
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1015 | h1015
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1016 | h1016
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1017 | h1017
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                        · linarith only [h1011, h1016, h1018, h834, h835, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h1018, h834, h835, hc13, hlam, hphi, u3elo3]
                      · linarith only [h1010, h1015, h1016, h1017, h834, h835, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1022 | h1022
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
                        · linarith only [h0, h1016, h1023, h834, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1016, h1023, h834, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1010, h1022, hlam]
                  · linarith only [h0, h1015, h834, hc13, hlam, hphi, u3elo2]
                · linarith only [h1013, h1014, h834, h835, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1029 | h1029
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1030 | h1030
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1033 | h1033
                        · linarith only [h1031, h1033, h834, h835, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1033, h834, h835, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1010, h1032, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1037 | h1037
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1038 | h1038
                        · linarith only [h0, h1031, h1038, h834, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1038, h834, h835, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1010, h1037, hlam]
                  · linarith only [h0, h1030, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1008, h1029, h835, hlam]
          · linarith only [h0, h1008, h1010, hlam]
        · linarith only [h0, h1009, h834, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1046 | h1046
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1047 | h1047
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1048 | h1048
            · linarith only [h1048, h834, h835, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1050 | h1050
              · linarith only [h1008, h1050, h834, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1052 | h1052
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1053 | h1053
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1054 | h1054
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1056 | h1056
                        · linarith only [h1048, h1054, h1056, h834, h835, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h1053, h1056, h834, h835, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1047, h1055, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1061 | h1061
                        · linarith only [h1008, h1048, h1061, h834, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                        · linarith only [h1008, h1054, h1060, h1061, h834, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1047, h1060, hlam]
                  · linarith only [h0, h1053, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1066 | h1066
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1067 | h1067
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1068 | h1068
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
                        · linarith only [h1067, h1069, h834, h835, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1069, h834, h835, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1047, h1068, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1073 | h1073
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1074 | h1074
                        · linarith only [h1008, h1073, h1074, h834, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1008, h1067, h1073, h1074, h834, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1047, h1073, hlam]
                  · linarith only [h0, h1066, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1079 | h1079
            · linarith only [h1079, h834, h835, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1081 | h1081
              · linarith only [h0, h1047, h1079, h1081, h834, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1083 | h1083
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1084 | h1084
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1085 | h1085
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1086 | h1086
                      · linarith only [h0, h1047, h1084, h1086, h834, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1088 | h1088
                        · linarith only [h1079, h1088, h834, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · linarith only [h1084, h1088, h834, h835, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1091 | h1091
                      · linarith only [h0, h1047, h1084, h1085, h1091, h834, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1093 | h1093
                        · linarith only [h0, h1085, h1093, h834, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1084, h1085, h1093, h834, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1084, h834, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1097 | h1097
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1098 | h1098
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1099 | h1099
                      · linarith only [h0, h1047, h1097, h1099, h834, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1101 | h1101
                        · linarith only [h1101, h834, h835, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h1097, h1101, h834, h835, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1104 | h1104
                      · linarith only [h0, h1047, h1097, h1098, h1104, h834, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1106 | h1106
                        · linarith only [h0, h1098, h1106, h834, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                        · linarith only [h0, h1097, h1098, h1106, h834, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1097, h834, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h1046, h834, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1111 | h1111
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1112 | h1112
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1113 | h1113
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1114 | h1114
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1115 | h1115
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1116 | h1116
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1117 | h1117
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1120 | h1120
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1123 | h1123
                            · linarith only [h1111, h1123, h834, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h1111, h1117, h1119, h1123, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1122, h834, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1112, h1113, h1115, h1121, h834, hc02, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h1114, h1120, hlam]
                    · linarith only [h1111, h1118, h1119, h834, hlam]
                  · linarith only [h0, h1113, h1118, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1135 | h1135
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1136 | h1136
                            · linarith only [h1111, h1117, h1136, h834, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1138 | h1138
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1139 | h1139
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1140 | h1140
                                  · linarith only [h1111, h1117, h1132, h1140, h834, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1142 | h1142
                                    · linarith only [h1111, h1117, h1132, h1138, h1142, hlam]
                                    · rcases h5bigk with h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1112, h1136, h834, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1144_1, u3elo1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1112, h834, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1144_1, u3elo1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1112, h834, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1144_1, u3elo1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1117, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1112, hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1139, hc35, hlam, hphi, ht01, ht0b, ht5b, p1144_1, u1elo4]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1112, h834, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1144_1, u3elo1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1136, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1114, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1133, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h0, h1114, hc35, hlam, hphi, ht01, ht0b, ht5b, p1144_1, u1elo1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1140, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1116, hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1135, hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1139, hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [hlam, p1144_0]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1142, hlam, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1111, h1117, h1132, h1138, hc34, hc45, hlam, hphi, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1132, h1136, h1138, hc34, hc45, hlam, hphi, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1138, h1140, hc34, hc45, hlam, hphi, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [h1142, hc34, hc45, hlam, hphi, p1144_1]
                                      · have p1144_0 := h1144c.1
                                        have p1144_1 := h1144c.2.1
                                        have p1144_2 := h1144c.2.2.1
                                        have p1144_3 := h1144c.2.2.2
                                        linarith only [hlam, p1144_0]
                                · linarith only [h1116, h1139, h834, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1115, h1138, h834, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1111, h1132, h1135, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1111, h1132, h1134, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1114, h1133, hlam]
                    · linarith only [h0, h1111, h1132, h834, hc02, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1131, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1112, h1116, h834, hlam]
            · linarith only [h1111, h1115, h834, hlam]
          · linarith only [h1112, h1113, h1114, h834, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1180 | h1180
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1181 | h1181
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1182 | h1182
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1183 | h1183
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
                  · linarith only [h0, h1111, h1113, h1184, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h1111, h1184, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1187 | h1187
                  · linarith only [h0, h1111, h1113, h1187, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h1111, h1187, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h1112, h1113, h1182, hlam]
            · linarith only [h0, h1111, h1113, h1181, hlam]
          · linarith only [h0, h1112, h1180, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1193 | h1193
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1194 | h1194
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1195 | h1195
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1196 | h1196
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1197 | h1197
                · linarith only [h1111, h1112, h1197, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1199 | h1199
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1200 | h1200
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1201 | h1201
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1204 | h1204
                            · linarith only [h1111, h1112, h1197, h1204, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1206 | h1206
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1207 | h1207
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1208 | h1208
                                  · linarith only [h1112, h1200, h1204, h1208, hc01, hlam, hphi, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1210 | h1210
                                    · linarith only [h1111, h1112, h1200, h1204, h1206, h1210, hlam]
                                    · rcases h5bigk with h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c | h1212c
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1112, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1196, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1212_1, u3elo0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1112, h1210, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1212_1, u1elo4]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1197, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1212_1, u1elo4]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1201, hc25, hlam, hphi, ht01, ht0b, ht5b, p1212_1, u1elo1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1203, h1210, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1212_1, u3elo1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1204, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1194, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1201, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1194, h1210, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1208, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1196, hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1203, hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1207, hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hlam, p1212_0]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1210, hlam, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1111, h1112, h1200, h1206, hc34, hc45, hlam, hphi, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1111, h1112, h1200, h1206, hc34, hc45, hlam, hphi, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1207, h1210, hc34, hc45, hlam, hphi, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [h1210, hc34, hc45, hlam, hphi, p1212_1]
                                      · have p1212_0 := h1212c.1
                                        have p1212_1 := h1212c.2.1
                                        have p1212_2 := h1212c.2.2.1
                                        have p1212_3 := h1212c.2.2.2
                                        linarith only [hlam, p1212_0]
                                · linarith only [h1196, h1207, h834, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1195, h1206, h834, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1203, h834, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1111, h1200, h1202, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1194, h1201, hlam]
                    · linarith only [h0, h1111, h1194, h1200, h834, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                  · linarith only [h0, h1199, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1245 | h1245
                · linarith only [h1111, h1112, h1245, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1247 | h1247
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1248 | h1248
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1249 | h1249
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1250 | h1250
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1251 | h1251
                          · linarith only [h1196, h1251, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1111, h1248, h1251, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1111, h1248, h1250, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1194, h1249, hlam]
                    · linarith only [h1111, h1247, h1248, h834, hlam]
                  · linarith only [h0, h1193, h1247, hlam]
            · linarith only [h1111, h1195, h834, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1259 | h1259
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1260 | h1260
              · linarith only [h1193, h1194, h1260, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1262 | h1262
                · linarith only [h1111, h1193, h1194, h1262, h834, hc23, hlam, hphi, u3elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1264 | h1264
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1265 | h1265
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1266 | h1266
                      · linarith only [h1193, h1194, h1266, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1269 | h1269
                          · linarith only [h1111, h1260, h1265, h1269, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1111, h1265, h1269, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1111, h1265, h1268, h834, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h1111, h1265, h834, hc12, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1111, h1193, h1264, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1111, h1259, h834, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1276 | h1276
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1277 | h1277
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1278 | h1278
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1279 | h1279
                · linarith only [h1111, h1112, h1279, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1281 | h1281
                  · linarith only [h1111, h1112, h1193, h1276, h1281, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h1111, h1281, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1193, h1276, h1278, hlam]
            · linarith only [h1111, h1112, h1193, h1276, h1277, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1286 | h1286
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1287 | h1287
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1288 | h1288
                · linarith only [h0, h1111, h1276, h1288, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1290 | h1290
                  · linarith only [h0, h1111, h1193, h1290, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                  · linarith only [h0, h1111, h1290, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1293 | h1293
                · linarith only [h1111, h1287, h1293, h834, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1295 | h1295
                  · linarith only [h0, h1193, h1295, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1111, h1295, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h1111, h1193, h1286, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1299 | h1299
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1300 | h1300
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1301 | h1301
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1302 | h1302
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1303 | h1303
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1304 | h1304
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1305 | h1305
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1306 | h1306
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1307 | h1307
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1308 | h1308
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1309 | h1309
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1310 | h1310
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1311 | h1311
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1312 | h1312
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1313 | h1313
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1314 | h1314
                                    · linarith only [h0, h1300, h1311, h1314, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · linarith only [h1111, h1299, h1308, h1310, h1314, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                                  · linarith only [h1111, h1299, h1308, h1310, h1313, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1303, h1312, hc23, hlam, hphi, u3elo0]
                              · linarith only [h1302, h1311, h834, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1111, h1299, h1304, h1310, hc04, hc15, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1111, h1299, h1307, h1308, h1309, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h1302, h1308, h834, hlam]
                      · linarith only [h0, h1301, h1307, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1324 | h1324
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1325 | h1325
                        · linarith only [h1305, h1306, h1325, hlam]
                        · linarith only [h0, h1300, h1302, h1325, h834, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1301, h1324, hlam]
                  · linarith only [h0, h1299, h1305, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1111, h1299, h1304, hlam]
              · linarith only [h1299, h1303, h834, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1332 | h1332
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1333 | h1333
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1334 | h1334
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1335 | h1335
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1336 | h1336
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1337 | h1337
                        · linarith only [h1302, h1334, h1337, h834, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1299, h1336, h1337, h834, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h1299, h1301, h1336, hc02, hc15, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1341 | h1341
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1342 | h1342
                        · linarith only [h1299, h1302, h1341, h1342, h834, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h1299, h1341, h1342, h834, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h1299, h1301, h1341, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1299, h1334, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1299, h1302, h1333, h834, hlam]
              · linarith only [h1299, h1332, h834, hlam]
          · linarith only [h0, h1299, h1301, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1350 | h1350
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1351 | h1351
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1354 | h1354
                  · linarith only [h0, h1300, h1354, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1299, h1354, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1111, h1299, h1353, hlam]
              · linarith only [h0, h1299, h1300, h1352, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1359 | h1359
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1360 | h1360
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1361 | h1361
                  · linarith only [h0, h1299, h1300, h1361, hc15, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h1299, h1361, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h1299, h1300, h1351, h1360, hlam]
              · linarith only [h0, h1299, h1300, h1359, hlam]
          · linarith only [h0, h1299, h1350, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1367 | h1367
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1368 | h1368
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1369 | h1369
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1370 | h1370
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1371 | h1371
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1373 | h1373
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1374 | h1374
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1376 | h1376
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1377 | h1377
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1378 | h1378
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1379 | h1379
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1380 | h1380
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1381 | h1381
                                    · linarith only [h0, h1367, h1378, h1381, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                    · linarith only [h0, h1367, h1378, h1380, h1381, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1384 | h1384
                                    · linarith only [h1378, h1380, h1384, hlam]
                                    · rcases h5bigk with h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1299, hlam, p1386_1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1299, hc25, hlam, hphi, ht01, ht0b, ht5b, p1386_1, u1elo4]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1370, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1386_1, u3elo0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1111, h1371, h1375, h1378, h1380, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1386_1, u3elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1386_1, u1elo4]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1374, hc25, hlam, hphi, ht01, ht0b, ht5b, p1386_1, u1elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1376, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1386_1, u3elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1375, h1377, h1378, h1380, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1386_1, u3elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1368, hlam, p1386_1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1374, hlam, p1386_1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h0, h1368, hc35, hlam, hphi, ht01, ht0b, ht5b, p1386_1, u1elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1380, hlam, p1386_1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1370, hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1376, hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1379, hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1384, hlam, p1386_1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1371, hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1377, hlam, p1386_0]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1299, h1371, h1375, h1377, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1386_1, u3elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [h1111, h1371, h1375, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1386_1, u3elo1]
                                      · have p1386_0 := h1386c.1
                                        have p1386_1 := h1386c.2.1
                                        have p1386_2 := h1386c.2.2.1
                                        have p1386_3 := h1386c.2.2.2
                                        linarith only [hlam, p1386_0]
                                · linarith only [h1370, h1379, h834, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1369, h1378, h834, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1111, h1371, h1377, hlam]
                          · linarith only [h1370, h1376, h834, hlam]
                        · linarith only [h1369, h1375, h834, hlam]
                      · linarith only [h0, h1368, h1374, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1418 | h1418
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
                        · linarith only [h1372, h1373, h1419, hlam]
                        · linarith only [h1369, h1419, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h1368, h1418, hlam]
                  · linarith only [h0, h1372, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1424 | h1424
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1425 | h1425
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1426 | h1426
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1427 | h1427
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1428 | h1428
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1429 | h1429
                            · linarith only [h1111, h1371, h1424, h1427, h1429, hc01, hlam, hphi, u1elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1431 | h1431
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1432 | h1432
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1433 | h1433
                                  · linarith only [h0, h1367, h1429, h1431, h1433, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1435 | h1435
                                    · linarith only [h0, h1111, h1367, h1429, h1431, h1435, hc01, hlam, hphi, u1elo1]
                                    · rcases h5bigk with h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c | h1437c
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1299, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1370, h1433, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1437_1, u3elo0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1370, h1435, h834, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1437_1, u3elo1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1371, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1428, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1437_1, u3elo1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1428, h1433, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1437_1, u3elo1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1428, h1435, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1437_1, u3elo1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1429, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1368, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1426, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h0, h1368, h1435, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1437_1, u1elo1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1433, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1370, hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1428, hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1432, hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [hlam, p1437_0]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1435, hlam, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1299, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1299, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1432, h1435, hc34, hc45, hlam, hphi, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [h1435, hc34, hc45, hlam, hphi, p1437_1]
                                      · have p1437_0 := h1437c.1
                                        have p1437_1 := h1437c.2.1
                                        have p1437_2 := h1437c.2.2.1
                                        have p1437_3 := h1437c.2.2.2
                                        linarith only [hlam, p1437_0]
                                · linarith only [h1370, h1432, h834, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1369, h1431, h834, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1428, h834, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1369, h1427, h834, hlam]
                      · linarith only [h0, h1368, h1426, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1468 | h1468
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1469 | h1469
                        · linarith only [h1424, h1425, h1469, hlam]
                        · linarith only [h0, h1367, h1369, h1469, h834, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h1368, h1468, hlam]
                  · linarith only [h0, h1424, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1474 | h1474
                · linarith only [h1369, h1370, h1474, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1476 | h1476
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1477 | h1477
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1478 | h1478
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1479 | h1479
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1480 | h1480
                          · linarith only [h1369, h1370, h1476, h1480, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                          · linarith only [h1480, h834, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1479, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1368, h1478, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1486 | h1486
                        · linarith only [h1476, h1477, h1486, hlam]
                        · linarith only [h1369, h1370, h1486, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1368, h1485, hlam]
                  · linarith only [h0, h1476, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1491 | h1491
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1492 | h1492
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1493 | h1493
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1494 | h1494
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1495 | h1495
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
                        · linarith only [h1369, h1491, h1493, h1496, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                        · linarith only [h1496, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1368, h1495, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
                        · linarith only [h1369, h1491, h1501, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                        · linarith only [h1501, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1299, h1368, h1500, hc01, hlam, hphi, u1elo4]
                  · linarith only [h0, h1493, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1369, h1491, h1492, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1510 | h1510
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                        · linarith only [h1369, h1511, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1511, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1368, h1510, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1515 | h1515
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1516 | h1516
                        · linarith only [h1369, h1516, h834, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1516, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1299, h1368, h1515, hc01, hlam, hphi, u1elo4]
                  · linarith only [h0, h1508, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1521 | h1521
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1522 | h1522
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1523 | h1523
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1524 | h1524
                        · linarith only [h1369, h1521, h1524, h834, hc01, hlam, hphi, u1elo1]
                        · linarith only [h1524, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1368, h1523, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1528 | h1528
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1529 | h1529
                        · linarith only [h1369, h1529, h834, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1529, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1368, h1528, hlam]
                  · linarith only [h0, h1521, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1534 | h1534
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1535 | h1535
              · linarith only [h1367, h1368, h1535, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1537 | h1537
                · linarith only [h1367, h1368, h1534, h1537, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1539 | h1539
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1540 | h1540
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1541 | h1541
                      · linarith only [h1367, h1368, h1541, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1543 | h1543
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1544 | h1544
                          · linarith only [h1535, h1544, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1544, h834, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1543, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1548 | h1548
                      · linarith only [h1367, h1368, h1548, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1550 | h1550
                        · linarith only [h1539, h1540, h1550, hlam]
                        · linarith only [h1534, h1550, hc13, hlam, hphi, u3elo0]
                  · linarith only [h0, h1539, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1554 | h1554
              · linarith only [h1367, h1368, h1534, h1554, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1556 | h1556
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1557 | h1557
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1558 | h1558
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1559 | h1559
                      · linarith only [h1367, h1368, h1559, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1561 | h1561
                        · linarith only [h1534, h1561, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1561, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1564 | h1564
                      · linarith only [h1367, h1368, h1564, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1566 | h1566
                        · linarith only [h1534, h1566, h834, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1566, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1557, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1571 | h1571
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1572 | h1572
                      · linarith only [h0, h1368, h1572, hc01, hlam, hphi, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1574 | h1574
                        · linarith only [h1534, h1574, h834, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1574, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1577 | h1577
                      · linarith only [h1367, h1368, h1577, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1579 | h1579
                        · linarith only [h1534, h1579, h834, hc01, hlam, hphi, u1elo2]
                        · linarith only [h1579, h834, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1570, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1583 | h1583
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1584 | h1584
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1585 | h1585
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1586 | h1586
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                  · linarith only [h1367, h1583, h1587, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h1587, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1590 | h1590
                  · linarith only [h1111, h1367, h1583, h1586, h1590, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1590, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1367, h1583, h1585, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1594 | h1594
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1595 | h1595
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1596 | h1596
                  · linarith only [h1367, h1583, h1596, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                  · linarith only [h0, h1596, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1367, h1583, h1584, h1595, hlam]
              · linarith only [h1367, h1583, h1594, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1601 | h1601
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1602 | h1602
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1603 | h1603
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
                  · linarith only [h0, h1367, h1604, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1604, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1607 | h1607
                  · linarith only [h0, h1367, h1607, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1607, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1610 | h1610
                · linarith only [h1601, h1602, h1610, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1612 | h1612
                  · linarith only [h0, h1367, h1612, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1612, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1615 | h1615
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1616 | h1616
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1617 | h1617
                  · linarith only [h0, h1367, h1617, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1617, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1601, h1615, h1616, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1621 | h1621
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1622 | h1622
                  · linarith only [h0, h1367, h1622, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1622, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1625 | h1625
                  · linarith only [h0, h1367, h1625, hc01, hlam, hphi, u1elo1]
                  · linarith only [h0, h1625, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3256000 in
theorem r1l7_11_13_25_L_0_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_0_L_0_H_I_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_0_L_0_H_I_x1 m hb1 hb3 hb5 h0

end R2N4
