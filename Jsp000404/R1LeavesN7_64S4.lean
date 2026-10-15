import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_64S3

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_I_L_0_L_R_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h882 | h882
  · rcases m.htr 0 1 4 (by decide) (by decide) with h883 | h883
    · linarith only [h0, h883, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h885 | h885
      · rcases m.htr 0 2 3 (by decide) (by decide) with h886 | h886
        · rcases m.htr 0 2 4 (by decide) (by decide) with h887 | h887
          · rcases m.htr 0 2 5 (by decide) (by decide) with h888 | h888
            · rcases m.htr 0 3 4 (by decide) (by decide) with h889 | h889
              · linarith only [h0, h882, h889, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h891 | h891
                · rcases m.htr 0 4 5 (by decide) (by decide) with h892 | h892
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h893 | h893
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                      · linarith only [h0, h882, h889, h893, h894, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
                        · linarith only [h0, h882, h893, h896, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h889, h891, h896, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h893, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h882, h883, h891, h892, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h901 | h901
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h903 | h903
                      · linarith only [h0, h882, h889, h902, h903, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h905 | h905
                        · linarith only [h882, h891, h902, h905, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h907 | h907
                          · linarith only [h887, h907, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi4]
                          · linarith only [h0, h887, h901, h907, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                    · linarith only [h0, h902, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h883, h885, h901, hlam]
            · linarith only [h887, h888, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h913 | h913
            · rcases m.htr 0 3 4 (by decide) (by decide) with h914 | h914
              · linarith only [h0, h882, h887, h914, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h916 | h916
                · rcases m.htr 0 4 5 (by decide) (by decide) with h917 | h917
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h918 | h918
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h919 | h919
                      · linarith only [h0, h882, h887, h914, h918, h919, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h921 | h921
                        · linarith only [h0, h882, h887, h918, h921, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h0, h882, h887, h916, h921, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h918, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h882, h883, h916, h917, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h927 | h927
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h928 | h928
                      · linarith only [h0, h882, h927, h928, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h930 | h930
                        · linarith only [h0, h882, h887, h916, h927, h930, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h932 | h932
                          · linarith only [h887, h913, h932, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                          · linarith only [h0, h882, h887, h926, h932, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h885, h926, h927, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h883, h885, h926, hlam]
            · linarith only [h0, h885, h913, hlam]
        · linarith only [h0, h882, h886, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h939 | h939
        · rcases m.htr 0 2 4 (by decide) (by decide) with h940 | h940
          · rcases m.htr 0 2 5 (by decide) (by decide) with h941 | h941
            · rcases m.htr 0 3 4 (by decide) (by decide) with h942 | h942
              · linarith only [h0, h882, h942, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h944 | h944
                · linarith only [h882, h885, h944, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h947 | h947
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h948 | h948
                      · linarith only [h0, h882, h942, h947, h948, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                        · linarith only [h882, h885, h944, h947, h950, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h952 | h952
                          · linarith only [h0, h940, h952, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h940, h946, h952, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                    · linarith only [h0, h940, h946, h947, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h957 | h957
                      · linarith only [h882, h885, h956, h957, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                        · linarith only [h882, h883, h944, h946, h956, h959, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h961 | h961
                          · linarith only [h0, h940, h961, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                            · linarith only [h882, h883, h946, h963, hc13, hc34, hlam, hphi]
                            · rcases h0bigk with h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c | h965c
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h883, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h885, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h883, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h883, h946, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h882, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h939, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h942, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h944, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h882, h956, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h940, hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h882, h942, h956, h963, hc23, hc45, hlam, hphi, ht34, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h946, hlam, p965_0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h941, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h941, hlam, p965_1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h882, h941, h956, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p965_1, u2elo1]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [h0, h941, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p965_1, u2elo1, u4ehi0]
                              · have p965_0 := h965c.1
                                have p965_1 := h965c.2.1
                                have p965_2 := h965c.2.2.1
                                have p965_3 := h965c.2.2.2
                                linarith only [hlam, p965_0]
                    · linarith only [h0, h882, h956, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h940, h941, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h993 | h993
            · rcases m.htr 0 3 4 (by decide) (by decide) with h994 | h994
              · linarith only [h0, h882, h994, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h996 | h996
                · linarith only [h882, h885, h996, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h998 | h998
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h999 | h999
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1000 | h1000
                      · linarith only [h1000, h882, h885, h940, h993, h994, h999, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1002 | h1002
                        · linarith only [h1002, h882, h885, h996, h999, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                          · linarith only [h1004, h940, h993, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                          · linarith only [h1004, h882, h885, h940, h993, h998, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h882, h999, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h940, h993, h998, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1009 | h1009
              · linarith only [h0, h1009, h882, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1011 | h1011
                · linarith only [h0, h1011, h882, h993, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1013 | h1013
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1014 | h1014
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1015 | h1015
                      · linarith only [h0, h1009, h1014, h1015, h882, h940, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                        · linarith only [h0, h1011, h1014, h1017, h882, h993, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1019 | h1019
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1020 | h1020
                            · rcases h0bigk with h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c | h1021c
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h0, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, h883, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h883, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h885, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h993, hc01, hlam, hphi, ht12, p1021_1, u2elo4]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, h993, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1021_1, u2elo4]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h940, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h993, hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h882, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h939, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1009, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1011, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h940, hc02, hlam, hphi, p1021_1, u2elo3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, h940, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1021_1, u2elo3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h940, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1021_1, u2elo3]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h0, h1014, h882, h993, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1021_1, u2elo4]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1014, h882, h993, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1021_1, u2elo4]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [h1013, hlam, p1021_1]
                              · have p1021_0 := h1021c.1
                                have p1021_1 := h1021c.2.1
                                have p1021_2 := h1021c.2.2.1
                                have p1021_3 := h1021c.2.2.2
                                linarith only [hlam, p1021_0]
                            · linarith only [h0, h1014, h1015, h1020, h882, h940, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1013, h1019, h940, hlam]
                    · linarith only [h0, h1014, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1050 | h1050
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1051 | h1051
                      · linarith only [h0, h1050, h1051, h882, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1053 | h1053
                        · linarith only [h0, h1050, h1053, h882, h940, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1055 | h1055
                          · linarith only [h1013, h1055, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h0, h1055, h882, h940, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1050, h882, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h882, h939, hlam]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1060 | h1060
    · linarith only [h0, h1060, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1062 | h1062
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1063 | h1063
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1064 | h1064
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1065 | h1065
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1066 | h1066
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1067 | h1067
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1068 | h1068
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1069 | h1069
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1070 | h1070
                      · linarith only [h1063, h1070, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1072 | h1072
                        · linarith only [h1066, h1069, h1070, h1072, h882, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1074 | h1074
                          · linarith only [h0, h1064, h1074, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h1064, h1068, h1074, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                    · linarith only [h0, h1062, h1069, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h1060, h1062, h1068, hlam]
                · linarith only [h1062, h1067, h882, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1080 | h1080
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1081 | h1081
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1083 | h1083
                      · linarith only [h0, h1063, h1066, h1083, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1086 | h1086
                          · linarith only [h0, h1064, h1086, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h1064, h1081, h1086, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                        · linarith only [h1066, h1080, h1085, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1062, h1081, h1082, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h1060, h1062, h1081, hlam]
                · linarith only [h1062, h1080, h882, hlam]
            · linarith only [h1064, h1065, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1094 | h1094
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1095 | h1095
              · linarith only [h1063, h1064, h1095, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1097 | h1097
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1098 | h1098
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1099 | h1099
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1100 | h1100
                      · linarith only [h1063, h1064, h1095, h1100, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1102 | h1102
                        · linarith only [h1063, h1064, h1102, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h1063, h1064, h1097, h1102, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1062, h1098, h1099, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h1060, h1062, h1098, hlam]
                · linarith only [h1062, h1097, h882, hlam]
            · linarith only [h0, h1062, h1094, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1109 | h1109
          · linarith only [h1063, h1109, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1111 | h1111
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1112 | h1112
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1113 | h1113
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1114 | h1114
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1115 | h1115
                    · linarith only [h0, h1063, h1115, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1062, h1114, h1115, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h1060, h1062, h1114, hlam]
                · linarith only [h0, h1062, h1109, h1112, h1113, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1121 | h1121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1122 | h1122
                    · linarith only [h0, h1063, h1122, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1062, h1121, h1122, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h1060, h1062, h1121, hlam]
                · linarith only [h0, h1062, h1063, h1120, hlam]
            · linarith only [h0, h1062, h1111, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1128 | h1128
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1129 | h1129
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1130 | h1130
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1131 | h1131
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1132 | h1132
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1133 | h1133
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1135 | h1135
                      · linarith only [h1128, h1135, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1137 | h1137
                        · linarith only [h0, h1128, h1131, h1135, h1137, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1139 | h1139
                          · linarith only [h0, h1129, h1139, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h1129, h1133, h1139, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                    · linarith only [h0, h1128, h1131, h1134, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1144 | h1144
                      · linarith only [h1128, h1144, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1146 | h1146
                        · linarith only [h0, h1128, h1131, h1144, h1146, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1148 | h1148
                          · linarith only [h1131, h1133, h1144, h1148, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                            · linarith only [h1131, h1133, h1150, hlam]
                            · rcases h0bigk with h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h882, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1060, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1062, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, p1152_1, u2elo0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1132, h1146, h1148, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1152_1, u2elo1, u4ehi2]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1131, h1144, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u2elo1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1131, h1133, h1144, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u2elo1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h882, hc01, hc13, hlam, hphi, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1128, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1128, h1131, h1144, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u2elo1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1128, h1131, h1133, h1144, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u2elo1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1133, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1129, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1131, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1133, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1062, hc01, hc15, hlam, hphi, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1130, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1132, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h1128, h1132, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1152_1, u2elo1, u4ehi0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                    · linarith only [h0, h1143, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1179 | h1179
                  · linarith only [h1131, h1132, h1179, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1181 | h1181
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1182 | h1182
                      · linarith only [h0, h1128, h1182, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi3]
                      · linarith only [h1131, h1132, h1182, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1181, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1186 | h1186
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1187 | h1187
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1188 | h1188
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1189 | h1189
                      · linarith only [h1128, h1131, h1186, h1189, hc02, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1191 | h1191
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1192 | h1192
                          · linarith only [h0, h1129, h1192, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h1129, h1187, h1192, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                        · linarith only [h1131, h1186, h1191, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h1129, h1187, h1188, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi4]
                  · linarith only [h1131, h1186, h1187, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1198 | h1198
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1199 | h1199
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1200 | h1200
                      · linarith only [h1128, h1131, h1200, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1202 | h1202
                        · linarith only [h0, h1062, h1128, h1186, h1202, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1204 | h1204
                          · linarith only [h0, h1129, h1204, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi4]
                          · linarith only [h0, h1129, h1198, h1204, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1, u4ehi2]
                    · linarith only [h0, h1128, h1186, h1199, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1208 | h1208
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1209 | h1209
                      · linarith only [h0, h1128, h1131, h1209, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1211 | h1211
                        · linarith only [h1128, h1186, h1211, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1213 | h1213
                          · linarith only [h1198, h1213, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1215 | h1215
                            · rcases h0bigk with h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h882, hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1060, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1062, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1216_1, u2elo1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1216_1, u2elo1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1216_1, u2elo1, u4ehi0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1216_1, u2elo1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h882, hc01, hc13, hlam, hphi, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1128, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1131, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1186, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1198, h1215, hc01, hc34, hlam, hphi, ht12, ht23, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1129, hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1198, h1215, hc03, hc34, hlam, hphi, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1198, hlam, p1216_0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1062, hc01, hc15, hlam, hphi, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h1130, hlam, p1216_1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, h1130, h882, hc01, hlam, hphi, ht12, p1216_1, u2elo1]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [h0, h1130, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1216_1, u2elo1, u4ehi0]
                              · have p1216_0 := h1216c.1
                                have p1216_1 := h1216c.2.1
                                have p1216_2 := h1216c.2.2.1
                                have p1216_3 := h1216c.2.2.2
                                linarith only [hlam, p1216_0]
                            · rcases h0bigk with h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c | h1242c
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h882, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1060, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1062, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht12, p1242_1, u2elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, h882, hc01, hlam, hphi, ht12, p1242_1, u2elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, h1129, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1242_1, u2elo1, u4ehi2]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1242_1, u2elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1131, hc01, hc34, hlam, hphi, ht12, ht23, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1128, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1131, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1186, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1060, hc01, hc14, hlam, hphi, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1129, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1131, h1215, hc03, hc45, hlam, hphi, ht34, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1198, hlam, p1242_0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1062, hc01, hc15, hlam, hphi, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h1130, hlam, p1242_1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, h1130, h882, hc01, hlam, hphi, ht12, p1242_1, u2elo1]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [h0, h1130, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1242_1, u2elo1, u4ehi0]
                              · have p1242_0 := h1242c.1
                                have p1242_1 := h1242c.2.1
                                have p1242_2 := h1242c.2.2.1
                                have p1242_3 := h1242c.2.2.2
                                linarith only [hlam, p1242_0]
                    · linarith only [h0, h1208, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h1129, h1130, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1270 | h1270
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1271 | h1271
              · linarith only [h1128, h1129, h1271, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1273 | h1273
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1274 | h1274
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1275 | h1275
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1276 | h1276
                      · linarith only [h1128, h1129, h1271, h1276, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1278 | h1278
                        · linarith only [h1128, h1129, h1278, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                        · linarith only [h1128, h1129, h1273, h1278, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1275, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1129, h1270, h1274, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1283 | h1283
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1284 | h1284
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1285 | h1285
                      · linarith only [h1128, h1129, h1285, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1287 | h1287
                        · linarith only [h1128, h1129, h1273, h1287, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1289 | h1289
                          · linarith only [h1129, h1270, h1289, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi4]
                          · linarith only [h1129, h1270, h1283, h1287, h1289, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h1284, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1129, h1270, h1283, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1294 | h1294
              · linarith only [h1128, h1129, h1294, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1296 | h1296
                · linarith only [h1128, h1270, h1296, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1298 | h1298
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1299 | h1299
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1300 | h1300
                      · linarith only [h1128, h1129, h1294, h1300, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1302 | h1302
                        · linarith only [h1128, h1129, h1296, h1302, h882, hc01, hlam, hphi, ht12, u2elo3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1304 | h1304
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1305 | h1305
                            · rcases h0bigk with h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c | h1306c
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h0, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h882, hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1060, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1062, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1270, h1304, hc01, hlam, hphi, ht12, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1270, h1304, h882, hc01, hlam, hphi, ht12, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1129, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1270, hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1299, h882, hc01, hc12, hlam, hphi, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1128, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1294, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1296, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1060, hc01, hc14, hlam, hphi, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1129, hc02, hlam, hphi, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1129, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [hlam, p1306_0]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1128, h1129, h1270, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1062, hc01, hc15, hlam, hphi, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1128, h1270, h1304, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1270, h1304, h882, hc01, hlam, hphi, ht12, p1306_1, u2elo3]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [h1298, hlam, p1306_1]
                              · have p1306_0 := h1306c.1
                                have p1306_1 := h1306c.2.1
                                have p1306_2 := h1306c.2.2.1
                                have p1306_3 := h1306c.2.2.2
                                linarith only [hlam, p1306_0]
                            · linarith only [h1128, h1129, h1300, h1305, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h1128, h1129, h1298, h1304, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1128, h1270, h1299, hc12, hlam, hphi, u2elo4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                      · linarith only [h1128, h1270, h1336, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                        · linarith only [h1128, h1270, h1338, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1340 | h1340
                          · linarith only [h1298, h1340, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3, u4ehi0]
                          · linarith only [h1128, h1129, h1340, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1128, h1129, h1335, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1344 | h1344
          · linarith only [h1128, h1344, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1346 | h1346
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1347 | h1347
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1348 | h1348
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1349 | h1349
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1350 | h1350
                    · linarith only [h1128, h1350, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1350, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1344, h1346, h1349, hlam]
                · linarith only [h1128, h1346, h1347, h1348, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2, u4ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1355 | h1355
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1356 | h1356
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1357 | h1357
                    · linarith only [h1128, h1357, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1357, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1344, h1346, h1356, hlam]
                · linarith only [h1128, h1346, h1355, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1362 | h1362
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1363 | h1363
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1364 | h1364
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
                    · linarith only [h1128, h1365, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1365, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1368 | h1368
                    · linarith only [h0, h1128, h1368, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1368, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1371 | h1371
                  · linarith only [h1362, h1363, h1371, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                    · linarith only [h0, h1128, h1373, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1373, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1376 | h1376
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1377 | h1377
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1378 | h1378
                    · linarith only [h0, h1128, h1378, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1378, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1362, h1376, h1377, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1382 | h1382
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1383 | h1383
                    · linarith only [h0, h1128, h1383, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1383, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1386 | h1386
                    · linarith only [h0, h1128, h1386, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1386, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_20_12_14_H_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2elo := hb2.1
  have h4ehi := hb4.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_0_L_R_x0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_0_L_R_x1 m hb0 hb2 hb4 h0

end R2N4
