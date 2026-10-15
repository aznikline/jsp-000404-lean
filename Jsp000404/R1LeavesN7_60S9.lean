import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_60S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3458000 in
set_option maxHeartbeats 3458000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h873 | h873
  · rcases m.htr 0 1 4 (by decide) (by decide) with h874 | h874
    · rcases m.htr 0 1 5 (by decide) (by decide) with h875 | h875
      · rcases m.htr 0 2 3 (by decide) (by decide) with h876 | h876
        · rcases m.htr 0 2 4 (by decide) (by decide) with h877 | h877
          · rcases m.htr 0 2 5 (by decide) (by decide) with h878 | h878
            · rcases m.htr 0 3 4 (by decide) (by decide) with h879 | h879
              · rcases m.htr 0 3 5 (by decide) (by decide) with h880 | h880
                · rcases m.htr 0 4 5 (by decide) (by decide) with h881 | h881
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h882 | h882
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h883 | h883
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h884 | h884
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h885 | h885
                          · linarith only [h0, h873, h885, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h879, h882, h885, hc23, hlam, hphi, u3elo0]
                        · linarith only [h0, h884, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h883, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h882, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h892 | h892
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h893 | h893
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h894 | h894
                          · linarith only [h0, h873, h894, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h879, h894, hc13, hlam, hphi, u3elo0]
                        · linarith only [h0, h893, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h892, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h891, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h900 | h900
                  · linarith only [h879, h880, h900, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h902 | h902
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h903 | h903
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h904 | h904
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h905 | h905
                          · linarith only [h0, h873, h905, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h879, h880, h905, hc13, hlam, hphi, u3elo4]
                        · linarith only [h0, h873, h902, h904, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h873, h902, h903, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h875, h879, h880, h902, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h911 | h911
                · rcases m.htr 0 4 5 (by decide) (by decide) with h912 | h912
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h913 | h913
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h914 | h914
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h916 | h916
                          · linarith only [h873, h879, h916, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h918 | h918
                            · linarith only [h0, h874, h916, h918, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h879, h911, h913, h918, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h873, h913, h915, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h873, h913, h914, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h913, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h879, h911, h912, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h925 | h925
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h927 | h927
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h928 | h928
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h929 | h929
                          · linarith only [h0, h873, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h931 | h931
                            · linarith only [h0, h874, h911, h929, h931, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h933 | h933
                              · linarith only [h0, h874, h933, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                              · linarith only [h0, h874, h925, h933, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h928, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h873, h926, h927, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h873, h926, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
                          · linarith only [h0, h873, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h944 | h944
                            · linarith only [h873, h911, h944, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h946 | h946
                              · linarith only [h0, h874, h925, h946, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h948 | h948
                                · linarith only [h873, h879, h939, h948, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h950 | h950
                                  · linarith only [h873, h911, h939, h950, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h952 | h952
                                    · linarith only [h0, h873, h877, h879, h925, h939, h952, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h954 | h954
                                      · linarith only [h873, h879, h925, h939, h954, hc23, hlam, hphi, u3elo3]
                                      · rcases h0bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, h873, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, h873, h879, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          rcases p956_3 (m.d 0 1) (by simp) with h964 | h964
                                          · linarith only [h0, h964, hlam]
                                          · linarith only [h873, h964, hlam]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          rcases p956_3 (m.d 0 1) (by simp) with h967 | h967
                                          · linarith only [h0, h967, hlam]
                                          · linarith only [h874, h967, hlam]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          rcases p956_3 (m.d 0 1) (by simp) with h970 | h970
                                          · linarith only [h0, h970, hlam]
                                          · linarith only [h875, h970, hlam]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h873, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h876, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h879, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h911, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h874, hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h877, hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, h873, h874, h939, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h925, hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h875, hlam, p956_0]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h878, hlam, p956_1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h873, h911, h939, hc23, hlam, hphi, p956_1, u3elo4]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [h0, h875, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p956_1, u2elo1]
                                        · have p956_0 := h956c.1
                                          have p956_1 := h956c.2.1
                                          have p956_2 := h956c.2.2.1
                                          have p956_3 := h956c.2.2.2
                                          linarith only [hlam, p956_0]
                        · linarith only [h0, h941, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h873, h877, h939, h940, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h873, h939, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · linarith only [h0, h875, h878, hlam]
          · linarith only [h0, h874, h877, hlam]
        · linarith only [h0, h873, h876, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h994 | h994
        · rcases m.htr 0 2 4 (by decide) (by decide) with h995 | h995
          · rcases m.htr 0 2 5 (by decide) (by decide) with h996 | h996
            · rcases m.htr 0 3 4 (by decide) (by decide) with h997 | h997
              · rcases m.htr 0 3 5 (by decide) (by decide) with h998 | h998
                · linarith only [h873, h875, h998, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1000, h873, h875, h997, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1004 | h1004
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1005 | h1005
                          · linarith only [h1004, h1005, h873, h875, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1002, h1005, h997, h998, hc23, hlam, hphi, u3elo4]
                        · linarith only [h1004, h996, hc12, hlam, hphi, u2elo0]
                      · linarith only [h0, h1002, h1003, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1002, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1011 | h1011
                · linarith only [h1011, h874, h875, h997, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1013 | h1013
                  · linarith only [h1013, h874, h875, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1015 | h1015
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1016 | h1016
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1017 | h1017
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1018 | h1018
                          · linarith only [h1018, h873, h997, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1020 | h1020
                            · linarith only [h1011, h1017, h1020, h873, h875, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                            · linarith only [h1015, h1018, h1020, h874, h875, hc23, hlam, hphi, u3elo4]
                        · linarith only [h0, h1017, h996, hlam]
                      · linarith only [h0, h1016, h874, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1015, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1026 | h1026
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1027 | h1027
                · linarith only [h0, h1027, h873, h996, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1029 | h1029
                  · linarith only [h0, h1026, h1029, h873, h996, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1031 | h1031
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1032 | h1032
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1033 | h1033
                        · linarith only [h0, h1031, h1033, h873, h996, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1031, h1033, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1031, h1032, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1031, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1038 | h1038
                · linarith only [h0, h1026, h1038, h874, h996, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1040 | h1040
                  · linarith only [h0, h1040, h874, h996, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1042 | h1042
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1043 | h1043
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1044 | h1044
                        · linarith only [h0, h1042, h1044, h873, h996, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1042, h1044, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1042, h1043, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1042, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h874, h995, hlam]
        · linarith only [h0, h873, h994, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1051 | h1051
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1052 | h1052
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1054 | h1054
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1055 | h1055
              · linarith only [h1055, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1057 | h1057
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1059 | h1059
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1060 | h1060
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1061 | h1061
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1062 | h1062
                          · linarith only [h1055, h1062, h873, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1059, h1062, h873, h874, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1059, h1060, h1061, h873, h874, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1053, h1060, hlam]
                    · linarith only [h0, h1059, h873, hc13, hlam, hphi, u3elo2]
                  · linarith only [h1057, h1058, h873, h874, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1069 | h1069
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1070 | h1070
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1071 | h1071
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1072 | h1072
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1073 | h1073
                          · linarith only [h0, h1073, h873, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1070, h1073, h873, h874, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1070, h1071, h1072, h873, h874, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1053, h1071, hlam]
                    · linarith only [h0, h1070, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1051, h1069, h874, hlam]
            · linarith only [h0, h1051, h1054, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1081 | h1081
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1082 | h1082
              · linarith only [h0, h1053, h1082, h873, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1085 | h1085
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1086 | h1086
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
                      · linarith only [h0, h1053, h1087, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h0, h1086, h1087, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1086, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1082, h1084, h1085, h873, h874, hc13, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1092 | h1092
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1093 | h1093
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1094 | h1094
                      · linarith only [h0, h1053, h1093, h1094, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1093, h1094, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1093, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h1051, h1092, h874, hlam]
            · linarith only [h0, h1051, h1081, hlam]
        · linarith only [h0, h1052, h873, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1101 | h1101
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1102 | h1102
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1103 | h1103
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1104 | h1104
              · linarith only [h1104, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1051, h1106, h873, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1108 | h1108
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1112 | h1112
                          · linarith only [h1104, h1112, h873, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1109, h1112, h873, h874, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h1103, h1111, hlam]
                      · linarith only [h0, h1102, h1110, hlam]
                    · linarith only [h0, h1109, h873, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                          · linarith only [h1119, h1121, h873, h874, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1118, h1121, h873, h874, hc23, hlam, hphi, u3elo3]
                        · linarith only [h0, h1103, h1120, hlam]
                      · linarith only [h0, h1102, h1119, hlam]
                    · linarith only [h0, h1118, h873, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1127 | h1127
              · linarith only [h1127, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
                · linarith only [h1051, h1129, h873, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1131 | h1131
                  · linarith only [h1102, h1103, h1131, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1134 | h1134
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1135 | h1135
                        · linarith only [h1103, h1135, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1133, h1135, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1133, h1134, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1133, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1140 | h1140
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1141 | h1141
              · linarith only [h1141, h873, h874, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1143 | h1143
                · linarith only [h1051, h1143, h873, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
                      · linarith only [h1102, h1147, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1146, h1147, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1146, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                  · linarith only [h1102, h1140, h1145, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1152 | h1152
              · linarith only [h0, h1102, h1152, h873, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1154 | h1154
                · linarith only [h0, h1140, h1154, h873, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1156 | h1156
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
                      · linarith only [h0, h1102, h1157, h1158, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1157, h1158, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1157, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1162 | h1162
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1163 | h1163
                      · linarith only [h0, h1102, h1162, h1163, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1162, h1163, h873, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1162, h873, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · linarith only [h0, h1101, h873, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1168 | h1168
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1169 | h1169
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1170 | h1170
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1171 | h1171
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1172 | h1172
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1173 | h1173
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1174 | h1174
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1175 | h1175
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1176 | h1176
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1177 | h1177
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1178 | h1178
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1179 | h1179
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1180 | h1180
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1181 | h1181
                              · linarith only [h1168, h1181, h873, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h1168, h1175, h1177, h1181, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1180, h873, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1170, h1173, h1179, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1168, h1177, h1178, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h1176, h1177, h873, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1170, h1176, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1190 | h1190
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1192 | h1192
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1193 | h1193
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1194 | h1194
                              · linarith only [h1168, h1175, h1194, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1196 | h1196
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1197 | h1197
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1198 | h1198
                                    · linarith only [h1168, h1175, h1190, h1198, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1200 | h1200
                                      · linarith only [h1168, h1175, h1190, h1196, h1200, hlam]
                                      · rcases h0bigk with h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h0, hlam, p1202_1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h873, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h873, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1202_1, u3elo1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h873, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1202_1, u3elo1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1202_1, u2elo1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h0, h1169, h1191, h1197, h873, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1202_1, u2elo1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          rcases p1202_3 (m.d 0 1) (by simp) with h1211 | h1211
                                          · linarith only [h0, h1211, hlam]
                                          · linarith only [h1168, h1211, hlam]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          rcases p1202_3 (m.d 0 1) (by simp) with h1214 | h1214
                                          · linarith only [h0, h1214, hlam]
                                          · linarith only [h1169, h1214, hlam]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1169, h1190, h1194, h1196, hc34, hlam, hphi, ht0b, ht45, ht5b, p1202_1, u0elo2]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1170, hlam, p1202_1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          rcases p1202_3 (m.d 0 1) (by simp) with h1220 | h1220
                                          · linarith only [h1220, h873, hlam]
                                          · linarith only [h1168, h1220, hlam]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          rcases p1202_3 (m.d 0 1) (by simp) with h1223 | h1223
                                          · linarith only [h1223, h873, hlam]
                                          · linarith only [h1169, h1223, hlam]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1168, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1171, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1173, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1175, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1169, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1172, hlam, p1202_1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h1174, hlam, p1202_0]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [h0, h1168, h1169, h1190, h1196, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1202_1, u2elo1]
                                        · have p1202_0 := h1202c.1
                                          have p1202_1 := h1202c.2.1
                                          have p1202_2 := h1202c.2.2.1
                                          have p1202_3 := h1202c.2.2.2
                                          linarith only [hlam, p1202_0]
                                  · linarith only [h1174, h1197, h873, hc23, hlam, hphi, u3elo1]
                                · linarith only [h1173, h1196, h873, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1168, h1190, h1193, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h1192, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1191, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1168, h1189, h1190, h873, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1168, h1189, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h1169, h1174, h873, hlam]
              · linarith only [h1168, h1173, h873, hlam]
            · linarith only [h1169, h1170, h1172, h873, hc23, hlam, hphi, u3elo1]
          · linarith only [h1168, h1170, h1171, h873, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1247 | h1247
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1248 | h1248
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1249 | h1249
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1250 | h1250
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1251 | h1251
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1252 | h1252
                    · linarith only [h1170, h1247, h1252, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1252, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1255 | h1255
                    · linarith only [h0, h1168, h1170, h1255, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1168, h1255, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h0, h1169, h1170, h1250, hlam]
              · linarith only [h0, h1168, h1170, h1249, hlam]
            · linarith only [h0, h1169, h1248, hlam]
          · linarith only [h0, h1168, h1247, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1262 | h1262
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1263 | h1263
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1264 | h1264
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1265 | h1265
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1266 | h1266
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1267 | h1267
                  · linarith only [h1168, h1169, h1267, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1269 | h1269
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1270 | h1270
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1271 | h1271
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1272 | h1272
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1273 | h1273
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1274 | h1274
                              · linarith only [h1168, h1267, h1274, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1276 | h1276
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1277 | h1277
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1278 | h1278
                                    · linarith only [h1168, h1169, h1270, h1274, h1278, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1280 | h1280
                                      · linarith only [h1168, h1169, h1270, h1274, h1276, h1280, hlam]
                                      · rcases h0bigk with h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c | h1282c
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h0, hlam, p1282_1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h873, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1169, h1269, h1273, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1282_1, u2elo1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1169, hlam, p1282_1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1282_1, u2elo1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h0, h873, hc01, hlam, hphi, ht12, p1282_1, u2elo1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          rcases p1282_3 (m.d 0 1) (by simp) with h1291 | h1291
                                          · linarith only [h0, h1291, hlam]
                                          · linarith only [h1168, h1291, hlam]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h0, h1168, h1169, h1270, h1276, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1282_1, u2elo1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1168, h1270, h1276, hc34, hlam, hphi, ht0b, ht45, ht5b, p1282_1, u0elo2]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1262, hlam, p1282_1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          rcases p1282_3 (m.d 0 1) (by simp) with h1298 | h1298
                                          · linarith only [h1298, h873, hlam]
                                          · linarith only [h1168, h1298, hlam]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1168, h1169, h1270, h1276, h873, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1282_1, u3elo1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1168, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1263, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1265, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1267, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1168, h1270, h1276, hc34, hlam, hphi, ht0b, ht45, ht5b, p1282_1, u0elo4]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1264, hlam, p1282_1]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [h1266, hlam, p1282_0]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          rcases p1282_3 (m.d 0 1) (by simp) with h1310 | h1310
                                          · linarith only [h1169, h1310, hlam]
                                          · linarith only [h1168, h1310, hlam]
                                        · have p1282_0 := h1282c.1
                                          have p1282_1 := h1282c.2.1
                                          have p1282_2 := h1282c.2.2.1
                                          have p1282_3 := h1282c.2.2.2
                                          linarith only [hlam, p1282_0]
                                  · linarith only [h1266, h1277, h873, hc23, hlam, hphi, u3elo1]
                                · linarith only [h1265, h1276, h873, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1266, h1273, h873, hlam]
                          · linarith only [h1168, h1270, h1272, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1168, h1270, h1271, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h0, h1168, h1270, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1168, h1262, h1269, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1321 | h1321
                  · linarith only [h1168, h1169, h1321, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1323 | h1323
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1324 | h1324
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1325 | h1325
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1326 | h1326
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1327 | h1327
                            · linarith only [h1266, h1327, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1168, h1324, h1327, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h1168, h1324, h1326, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                        · linarith only [h0, h1168, h1324, h1325, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h1168, h1323, h1324, h873, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h1262, h1323, hlam]
              · linarith only [h1168, h1265, h873, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1335 | h1335
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1336 | h1336
                · linarith only [h1262, h1264, h1336, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1338 | h1338
                  · linarith only [h1168, h1262, h1264, h1338, h873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1340 | h1340
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1341 | h1341
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
                        · linarith only [h1168, h1262, h1264, h1341, h1342, h873, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h1168, h1341, h1342, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                      · linarith only [h1168, h1340, h1341, h873, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h1262, h1340, hc12, hlam, hphi, u2elo0]
              · linarith only [h1168, h1335, h873, hlam]
          · linarith only [h1168, h1262, h1263, h873, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1349 | h1349
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1350 | h1350
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1351 | h1351
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1352 | h1352
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1353 | h1353
                  · linarith only [h1168, h1169, h1353, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h1169, h1262, h1350, h1355, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1168, h1355, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h1262, h1350, h1352, hlam]
              · linarith only [h1168, h1169, h1262, h1350, h1351, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1360 | h1360
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1361 | h1361
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1362 | h1362
                  · linarith only [h0, h1168, h1350, h1362, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1364 | h1364
                    · linarith only [h0, h1168, h1262, h1364, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1168, h1364, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1367 | h1367
                  · linarith only [h1168, h1361, h1367, h873, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1369 | h1369
                    · linarith only [h0, h1168, h1262, h1369, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1168, h1369, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h1168, h1262, h1360, hlam]
          · linarith only [h0, h1168, h1349, hlam]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1374 | h1374
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1375 | h1375
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1376 | h1376
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1377 | h1377
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1378 | h1378
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1379 | h1379
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1380 | h1380
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1381 | h1381
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1382 | h1382
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1383 | h1383
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1386 | h1386
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1387 | h1387
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1388 | h1388
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1389 | h1389
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1390 | h1390
                                      · linarith only [h1375, h1387, h1390, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h1168, h1374, h1381, h1384, h1386, h1390, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · linarith only [h1168, h1374, h1381, h1384, h1386, h1389, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                  · linarith only [h1379, h1388, hc23, hlam, hphi, u3elo0]
                                · linarith only [h1378, h1387, hc23, hlam, hphi, u3elo0]
                              · linarith only [h1168, h1380, h1386, hlam]
                            · linarith only [h1374, h1383, h1385, h873, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                          · linarith only [h1378, h1384, h873, hlam]
                        · linarith only [h0, h1374, h1383, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                      · linarith only [h1374, h1381, h1382, h873, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                    · linarith only [h0, h1374, h1381, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1168, h1374, h1380, hlam]
                · linarith only [h1374, h1379, h873, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1404 | h1404
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1405 | h1405
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1407 | h1407
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1408 | h1408
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1409 | h1409
                          · linarith only [h1378, h1406, h1409, h873, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h1374, h1408, h1409, h873, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h0, h1408, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1374, h1376, h1406, h1407, h873, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                    · linarith only [h0, h1374, h1406, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1374, h1378, h1405, h873, hlam]
                · linarith only [h1374, h1404, h873, hlam]
            · linarith only [h1374, h1375, h1377, h873, hc23, hlam, hphi, u3elo1]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1418 | h1418
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1419 | h1419
              · linarith only [h1375, h1376, h1419, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1421 | h1421
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1422 | h1422
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1423 | h1423
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1424 | h1424
                      · linarith only [h1375, h1376, h1424, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1424, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1374, h1375, h1423, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h1168, h1374, h1422, hlam]
                · linarith only [h1374, h1421, h873, hlam]
            · linarith only [h1374, h1375, h1418, h873, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1431 | h1431
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1432 | h1432
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1433 | h1433
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1434 | h1434
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1436 | h1436
                    · linarith only [h1168, h1375, h1431, h1436, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1374, h1436, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1168, h1374, h1435, hlam]
                · linarith only [h1168, h1374, h1375, h1431, h1434, hlam]
              · linarith only [h1375, h1431, h1433, hlam]
            · linarith only [h1168, h1374, h1431, h1432, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1443 | h1443
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1444 | h1444
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1447 | h1447
                    · linarith only [h1375, h1447, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1374, h1447, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · linarith only [h0, h1374, h1431, h1446, hlam]
                · linarith only [h0, h1374, h1431, h1444, h1445, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1452 | h1452
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1453 | h1453
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
                    · linarith only [h0, h1374, h1375, h1454, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1374, h1454, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                  · linarith only [h1374, h1444, h1453, h873, hlam]
                · linarith only [h0, h1374, h1375, h1452, hlam]
            · linarith only [h0, h1374, h1443, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1460 | h1460
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1461 | h1461
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1462 | h1462
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1463 | h1463
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1465 | h1465
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1467 | h1467
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1468 | h1468
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1469 | h1469
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1470 | h1470
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1471 | h1471
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1472 | h1472
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1473 | h1473
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1474 | h1474
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1475 | h1475
                                      · linarith only [h1460, h1472, h1475, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                                      · linarith only [h0, h1460, h1472, h1474, h1475, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1478 | h1478
                                      · linarith only [h0, h1460, h1463, h1474, h1478, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                                      · rcases h0bigk with h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c | h1480c
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h0, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h873, hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1168, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1374, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1480_1, u2elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h0, h873, hc01, hlam, hphi, ht12, p1480_1, u2elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h0, h1374, h1465, hc01, hlam, hphi, ht12, p1480_1, u2elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h0, h1374, hc01, hlam, hphi, ht12, p1480_1, u2elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1460, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1374, h1465, h873, hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1374, h873, hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1168, h1469, hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1461, hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1463, hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1168, h1374, h1469, hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1374, h1469, h1471, hc01, hlam, hphi, ht12, ht23, p1480_1, u3elo1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1462, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1464, hlam, p1480_0]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [h1465, hlam, p1480_1]
                                        · have p1480_0 := h1480c.1
                                          have p1480_1 := h1480c.2.1
                                          have p1480_2 := h1480c.2.2.1
                                          have p1480_3 := h1480c.2.2.2
                                          linarith only [hlam, p1480_0]
                                  · linarith only [h1464, h1473, h873, hc23, hlam, hphi, u3elo1]
                                · linarith only [h1463, h1472, h873, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1168, h1465, h1471, hlam]
                            · linarith only [h1464, h1470, h873, hlam]
                          · linarith only [h1463, h1469, h873, hlam]
                        · linarith only [h0, h1462, h1468, hlam]
                      · linarith only [h0, h1467, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1466, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1514 | h1514
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1515 | h1515
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1516 | h1516
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1517 | h1517
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1518 | h1518
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1519 | h1519
                              · linarith only [h1168, h1465, h1517, h1519, hc01, hlam, hphi, ht12, ht23, u3elo1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1521 | h1521
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1522 | h1522
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1523 | h1523
                                    · linarith only [h1168, h1461, h1519, h1523, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1525 | h1525
                                      · linarith only [h0, h1168, h1460, h1519, h1521, h1525, hc01, hlam, hphi, ht12, u2elo1]
                                      · rcases h0bigk with h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c | h1527c
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, hlam, p1527_1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h873, hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1168, hlam, p1527_1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1374, hlam, p1527_1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, hc01, hlam, hphi, ht12, p1527_1, u2elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, h873, hc01, hlam, hphi, ht12, p1527_1, u2elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, h1168, hc01, hlam, hphi, ht12, p1527_1, u2elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, h1374, hc01, hlam, hphi, ht12, p1527_1, u2elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hc01, hlam, hphi, ht12, ht23, p1527_1, u3elo0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1460, hlam, p1527_1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1168, h873, hc01, hlam, hphi, ht12, ht23, p1527_1, u3elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1374, h873, hc01, hlam, hphi, ht12, ht23, p1527_1, u3elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h0, h1168, h1460, h1519, h1522, h1525, hc01, hc34, hc45, hlam, hphi, ht12, p1527_1, u2elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1461, hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1463, hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1465, hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1374, h1518, hc01, hlam, hphi, ht12, ht23, p1527_1, u3elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1462, hlam, p1527_1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1464, hlam, p1527_0]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [h1168, h1374, h1518, hc01, hlam, hphi, ht12, ht23, p1527_1, u3elo1]
                                        · have p1527_0 := h1527c.1
                                          have p1527_1 := h1527c.2.1
                                          have p1527_2 := h1527c.2.2.1
                                          have p1527_3 := h1527c.2.2.2
                                          linarith only [hlam, p1527_0]
                                  · linarith only [h1464, h1522, h873, hc23, hlam, hphi, u3elo1]
                                · linarith only [h1463, h1521, h873, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1464, h1518, h873, hlam]
                          · linarith only [h1517, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1516, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h0, h1461, h1515, hlam]
                    · linarith only [h0, h1514, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1560 | h1560
                  · linarith only [h1463, h1464, h1560, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1562 | h1562
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1563 | h1563
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1564 | h1564
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1565 | h1565
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1566 | h1566
                            · linarith only [h1464, h1566, hc03, hlam, hphi, u3elo1]
                            · linarith only [h1566, h873, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h1463, h1565, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h1462, h1564, hc12, hlam, hphi, u2elo0]
                      · linarith only [h0, h1563, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1562, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1573 | h1573
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1574 | h1574
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1575 | h1575
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1576 | h1576
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1577 | h1577
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1578 | h1578
                          · linarith only [h1463, h1578, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1578, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1462, h1575, h1577, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1461, h1576, hlam]
                    · linarith only [h0, h1575, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1463, h1573, h1574, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1585 | h1585
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1586 | h1586
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1587 | h1587
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1588 | h1588
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1589 | h1589
                          · linarith only [h1463, h1589, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1589, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h1588, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1461, h1586, h1587, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1586, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1595 | h1595
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1596 | h1596
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1597 | h1597
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1598 | h1598
                          · linarith only [h1463, h1595, h1598, h873, hc01, hlam, hphi, ht12, u2elo1]
                          · linarith only [h1598, h873, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1462, h1595, h1597, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h1596, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1595, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1604 | h1604
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1605 | h1605
                · linarith only [h1460, h1462, h1605, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1607 | h1607
                  · linarith only [h1461, h1462, h1607, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1609 | h1609
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1610 | h1610
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1611 | h1611
                        · linarith only [h1462, h1611, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1611, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1461, h1609, h1610, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1460, h1462, h1609, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1616 | h1616
                · linarith only [h1461, h1462, h1604, h1616, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1618 | h1618
                  · linarith only [h1461, h1462, h1618, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1620 | h1620
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1621 | h1621
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1622 | h1622
                        · linarith only [h1462, h1622, hc02, hlam, hphi, u2elo1]
                        · linarith only [h0, h1622, hc01, hlam, hphi, ht12, u2elo4]
                      · linarith only [h1461, h1620, h1621, h873, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1620, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1627 | h1627
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1628 | h1628
              · linarith only [h1460, h1461, h1628, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1630 | h1630
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1631 | h1631
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1632 | h1632
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1633 | h1633
                      · linarith only [h1461, h1633, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1633, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1460, h1632, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1460, h1461, h1628, h1630, h1631, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1638 | h1638
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1639 | h1639
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1640 | h1640
                      · linarith only [h1460, h1461, h1640, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1640, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1460, h1639, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1461, h1627, h1638, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1645 | h1645
              · linarith only [h1460, h1461, h1645, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1647 | h1647
                · linarith only [h1460, h1627, h1647, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1649 | h1649
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1650 | h1650
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1651 | h1651
                      · linarith only [h1461, h1651, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1651, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1460, h1650, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1655 | h1655
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1656 | h1656
                      · linarith only [h1461, h1656, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1656, hc01, hlam, hphi, ht12, u2elo3]
                    · linarith only [h0, h1460, h1655, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1660 | h1660
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1661 | h1661
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1662 | h1662
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1663 | h1663
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1664 | h1664
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1665 | h1665
                    · linarith only [h1460, h1660, h1665, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1665, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1668 | h1668
                    · linarith only [h1460, h1660, h1668, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1668, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1460, h1661, h1663, hlam]
              · linarith only [h1460, h1660, h1662, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1673 | h1673
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1674 | h1674
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1675 | h1675
                  · linarith only [h1660, h1661, h1675, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1677 | h1677
                    · linarith only [h1460, h1660, h1677, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1677, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1680 | h1680
                  · linarith only [h1460, h1660, h1674, h1680, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1682 | h1682
                    · linarith only [h1460, h1660, h1682, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1682, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1460, h1660, h1673, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h1686 | h1686
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1687 | h1687
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1688 | h1688
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1689 | h1689
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1690 | h1690
                    · linarith only [h1460, h1686, h1690, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1690, hc01, hlam, hphi, ht12, u2elo2]
                  · linarith only [h1660, h1686, h1689, hlam]
                · linarith only [h1660, h1686, h1687, h1688, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1695 | h1695
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1696 | h1696
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1697 | h1697
                    · linarith only [h1460, h1686, h1697, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h0, h1697, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1460, h1686, h1687, h1696, hlam]
                · linarith only [h1460, h1686, h1695, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1703 | h1703
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1704 | h1704
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1705 | h1705
                    · linarith only [h1460, h1705, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1705, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1708 | h1708
                    · linarith only [h0, h1460, h1708, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1708, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1711 | h1711
                  · linarith only [h1702, h1703, h1711, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1713 | h1713
                    · linarith only [h0, h1460, h1713, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1713, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h1716 | h1716
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1717 | h1717
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1718 | h1718
                    · linarith only [h0, h1460, h1718, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1718, hc01, hlam, hphi, ht12, ht23, u3elo2]
                  · linarith only [h1702, h1716, h1717, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1722 | h1722
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1723 | h1723
                    · linarith only [h0, h1460, h1723, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1723, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1726 | h1726
                    · linarith only [h0, h1460, h1726, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h1726, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3458000 in
set_option maxHeartbeats 3458000 in
theorem r1l7_20_12_13_15_M_LI_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_M_LI_L_0_L_0_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_M_LI_L_0_L_0_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
