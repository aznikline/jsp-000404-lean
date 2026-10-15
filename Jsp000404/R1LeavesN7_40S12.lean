import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h878 | h878
  · rcases m.htr 0 1 5 (by decide) (by decide) with h879 | h879
    · rcases m.htr 0 2 3 (by decide) (by decide) with h880 | h880
      · linarith only [h0, h1, h880, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h882 | h882
        · rcases m.htr 0 2 5 (by decide) (by decide) with h883 | h883
          · rcases m.htr 0 3 4 (by decide) (by decide) with h884 | h884
            · rcases m.htr 0 3 5 (by decide) (by decide) with h885 | h885
              · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
                · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                  · linarith only [h0, h880, h887, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h889 | h889
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h890 | h890
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h891 | h891
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h892 | h892
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h893 | h893
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                                  · linarith only [h0, h1, h887, h889, h896, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h878, h893, h896, hc24, hlam, hphi, u4elo0]
                                · linarith only [h0, h1, h887, h895, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h0, h1, h887, h894, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h886, h893, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h1, h892, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h891, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h883, h889, h890, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h880, h882, h889, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h906 | h906
                  · linarith only [h0, h1, h880, h906, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h908 | h908
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h909 | h909
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h910 | h910
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h911 | h911
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h912 | h912
                            · linarith only [h886, h912, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h914 | h914
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h915 | h915
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h916 | h916
                                  · linarith only [h878, h886, h908, h916, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h918 | h918
                                    · linarith only [h878, h886, h908, h914, h918, hlam]
                                    · rcases h0bigk with h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c | h920c
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h0, h1, h906, h909, h914, h916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p920_1]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h1, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h924 | h924
                                        · rcases p920_3 (m.d 0 2) (by simp) with h925 | h925
                                          · linarith only [h0, h925, hlam]
                                          · linarith only [h882, h925, hlam]
                                        · linarith only [h878, h924, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h929 | h929
                                        · rcases p920_3 (m.d 0 2) (by simp) with h930 | h930
                                          · linarith only [h0, h930, hlam]
                                          · linarith only [h883, h930, hlam]
                                        · linarith only [h879, h929, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h0, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h880, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h937 | h937
                                        · rcases p920_3 (m.d 0 2) (by simp) with h938 | h938
                                          · rcases p920_3 (m.d 0 3) (by simp) with h939 | h939
                                            · rcases p920_3 (m.d 0 4) (by simp) with h940 | h940
                                              · linarith only [h882, h940, hlam]
                                              · rcases p920_3 (m.d 0 5) (by simp) with h942 | h942
                                                · linarith only [h883, h942, hlam]
                                                · linarith only [h886, h942, hlam]
                                            · linarith only [h884, h939, hlam]
                                          · linarith only [h882, h938, hlam]
                                        · linarith only [h878, h937, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h948 | h948
                                        · rcases p920_3 (m.d 0 2) (by simp) with h949 | h949
                                          · rcases p920_3 (m.d 0 3) (by simp) with h950 | h950
                                            · rcases p920_3 (m.d 0 4) (by simp) with h951 | h951
                                              · linarith only [h882, h951, hlam]
                                              · rcases p920_3 (m.d 0 5) (by simp) with h953 | h953
                                                · linarith only [h883, h953, hlam]
                                                · rcases h0emin with h955 | h955 | h955 | h955 | h955
                                                  · rcases h1bigk with h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c | h956c
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h1, h906, h909, h914, h916, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h1, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      rcases p956_3 (m.d 0 1) (by simp) with h960 | h960
                                                      · rcases p956_3 (m.d 1 2) (by simp) with h961 | h961
                                                        · linarith only [h0, h961, hlam]
                                                        · linarith only [h908, h961, hlam]
                                                      · linarith only [h960, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      rcases p956_3 (m.d 0 1) (by simp) with h965 | h965
                                                      · rcases p956_3 (m.d 1 2) (by simp) with h966 | h966
                                                        · linarith only [h0, h966, hlam]
                                                        · linarith only [h909, h966, hlam]
                                                      · linarith only [h965, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h906, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, h1, h906, h908, h914, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, h1, h906, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h906, h955, hc23, hlam, ht01, ht12, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      rcases p956_3 (m.d 0 1) (by simp) with h976 | h976
                                                      · linarith only [h1, h976, hlam]
                                                      · linarith only [h0, h976, hlam]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, h1, h878, h886, hlam, p920_1, p956_2]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, h1, h879, hlam, p920_1, p956_2]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h878, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h908, hlam, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h910, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h912, hlam, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h879, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h909, hlam, p956_1]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h911, hlam, p956_0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [h0, h879, h908, h914, hc34, hlam, hphi, ht0b, ht45, ht5b, p920_1, p956_1, u0elo0]
                                                    · have p956_0 := h956c.1
                                                      have p956_1 := h956c.2.1
                                                      have p956_2 := h956c.2.2.1
                                                      have p956_3 := h956c.2.2.2
                                                      linarith only [hlam, p956_0]
                                                  · rcases h1bigk with h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c | h992c
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h1, h906, hc12, hc23, hlam, hphi, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h1, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      rcases p992_3 (m.d 0 1) (by simp) with h996 | h996
                                                      · rcases p992_3 (m.d 1 2) (by simp) with h997 | h997
                                                        · linarith only [h0, h997, hlam]
                                                        · linarith only [h908, h997, hlam]
                                                      · linarith only [h996, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      rcases p992_3 (m.d 0 1) (by simp) with h1001 | h1001
                                                      · rcases p992_3 (m.d 1 2) (by simp) with h1002 | h1002
                                                        · linarith only [h0, h1002, hlam]
                                                        · linarith only [h1002, h909, hlam]
                                                      · linarith only [h1001, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h906, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h1, h906, h908, h914, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h1, h906, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h906, h955, hc23, hlam, ht01, ht12, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      rcases p992_3 (m.d 0 1) (by simp) with h1012 | h1012
                                                      · linarith only [h1, h1012, hlam]
                                                      · linarith only [h0, h1012, hlam]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h1, h878, h886, hlam, p920_1, p992_2]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h1, h879, hlam, p920_1, p992_2]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h878, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h908, hlam, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h910, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h912, hlam, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h879, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h909, hlam, p992_1]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h911, hlam, p992_0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [h0, h879, h908, h914, hc34, hlam, hphi, ht0b, ht45, ht5b, p920_1, p992_1, u0elo0]
                                                    · have p992_0 := h992c.1
                                                      have p992_1 := h992c.2.1
                                                      have p992_2 := h992c.2.2.1
                                                      have p992_3 := h992c.2.2.2
                                                      linarith only [hlam, p992_0]
                                                  · rcases h1bigk with h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c | h1028c
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h1, h906, hc12, hc23, hlam, hphi, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h1, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      rcases p1028_3 (m.d 0 1) (by simp) with h1032 | h1032
                                                      · rcases p1028_3 (m.d 1 2) (by simp) with h1033 | h1033
                                                        · linarith only [h0, h1033, hlam]
                                                        · linarith only [h1033, h908, hlam]
                                                      · linarith only [h1032, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      rcases p1028_3 (m.d 0 1) (by simp) with h1037 | h1037
                                                      · rcases p1028_3 (m.d 1 2) (by simp) with h1038 | h1038
                                                        · linarith only [h0, h1038, hlam]
                                                        · linarith only [h1038, h909, hlam]
                                                      · linarith only [h1037, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h906, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h1, h906, h908, h914, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h1, h906, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h906, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1028_1, p920_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      rcases p1028_3 (m.d 0 1) (by simp) with h1048 | h1048
                                                      · linarith only [h1, h1048, hlam]
                                                      · linarith only [h0, h1048, hlam]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h1, h878, h886, hlam, p1028_2, p920_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h1, h879, hlam, p1028_2, p920_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h878, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h908, hlam, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h910, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h912, hlam, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h879, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h909, hlam, p1028_1]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h911, hlam, p1028_0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [h0, h879, h908, h914, hc34, hlam, hphi, ht0b, ht45, ht5b, p1028_1, p920_1, u0elo0]
                                                    · have p1028_0 := h1028c.1
                                                      have p1028_1 := h1028c.2.1
                                                      have p1028_2 := h1028c.2.2.1
                                                      have p1028_3 := h1028c.2.2.2
                                                      linarith only [hlam, p1028_0]
                                                  · linarith only [h886, h955, hlam, ht01, ht12, ht23, ht34, u4elo4]
                                                  · linarith only [h0, h1, h955, hc13, hlam, ht01, p920_1]
                                            · linarith only [h885, h950, hlam]
                                          · linarith only [h883, h949, hlam]
                                        · linarith only [h879, h948, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p920_1, u0elo2]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h882, h914, hc34, hlam, hphi, ht0b, ht45, ht5b, p920_1, u0elo2]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h1072 | h1072
                                        · linarith only [h1, h1072, hlam]
                                        · linarith only [h1072, h878, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        rcases p920_3 (m.d 0 1) (by simp) with h1075 | h1075
                                        · linarith only [h1, h1075, hlam]
                                        · linarith only [h1075, h879, hlam]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h878, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h882, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h884, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h886, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h879, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h883, hlam, p920_1]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h885, hlam, p920_0]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [h878, h886, h908, h914, hc34, hlam, hphi, p920_1, u4elo4]
                                      · have p920_0 := h920c.1
                                        have p920_1 := h920c.2.1
                                        have p920_2 := h920c.2.2.1
                                        have p920_3 := h920c.2.2.2
                                        linarith only [hlam, p920_0]
                                · linarith only [h0, h1, h906, h908, h914, h915, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h1, h906, h914, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h1, h908, h911, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h908, h910, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h883, h908, h909, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h1, h882, h906, h908, hc12, hc23, hlam, hphi]
              · linarith only [h1, h879, h885, hlam]
            · linarith only [h0, h1, h884, hc12, hlam, hphi, ht23, ht34, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1096 | h1096
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1097 | h1097
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1098 | h1098
                · linarith only [h1098, h882, h883, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h0, h1100, h880, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
                      · linarith only [h0, h1103, h883, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1105 | h1105
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1106 | h1106
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1107 | h1107
                            · linarith only [h1098, h1107, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1110 | h1110
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1111 | h1111
                                  · linarith only [h0, h1098, h1102, h1111, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h1109, h1111, h882, h883, hc34, hlam, hphi, u4elo4]
                                · linarith only [h1, h1100, h1106, h1110, h879, hlam]
                              · linarith only [h1, h1100, h1106, h1109, h879, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h1, h1102, h1103, h1106, h879, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h1102, h1103, h1105, h879, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1098, h1102, h882, h883, hc12, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h1, h1097, h879, hlam]
            · linarith only [h1, h1096, h879, h882, h883, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1121 | h1121
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1122 | h1122
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1123 | h1123
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1124 | h1124
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1125 | h1125
                  · linarith only [h0, h1125, h880, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1127 | h1127
                    · linarith only [h0, h1127, h882, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1129 | h1129
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1130 | h1130
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1131 | h1131
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1132 | h1132
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1134 | h1134
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1136 | h1136
                                    · rcases h0bigk with h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c | h1137c
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, h1, h1125, h1129, h1134, h1136, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1137_1]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h1, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, h1, h1125, h1129, h1134, h1136, h882, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1137_1]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        rcases p1137_3 (m.d 0 1) (by simp) with h1142 | h1142
                                        · rcases p1137_3 (m.d 0 2) (by simp) with h1143 | h1143
                                          · linarith only [h0, h1143, hlam]
                                          · linarith only [h1121, h1143, hlam]
                                        · linarith only [h1142, h879, hlam]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h880, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h882, hlam, p1137_1]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h882, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1137_1, u4elo2]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1137_1, u0elo2]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, h1129, h1134, h1136, hc45, hlam, hphi, ht0b, ht5b, p1137_1, u0elo2]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, h1129, h1134, h1136, h882, hc45, hlam, hphi, ht0b, ht5b, p1137_1, u0elo2]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        rcases p1137_3 (m.d 0 1) (by simp) with h1156 | h1156
                                        · linarith only [h1, h1156, hlam]
                                        · linarith only [h1156, h879, hlam]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h878, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h0, h1129, h1134, h1136, hc45, hlam, hphi, ht0b, ht5b, p1137_1, u0elo3]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h1122, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        rcases p1137_3 (m.d 0 1) (by simp) with h1163 | h1163
                                        · rcases p1137_3 (m.d 0 2) (by simp) with h1164 | h1164
                                          · linarith only [h1164, h882, hlam]
                                          · linarith only [h1121, h1164, hlam]
                                        · linarith only [h1163, h879, hlam]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h879, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h1121, hlam, p1137_1]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h1123, hlam, p1137_0]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [h1124, hlam, p1137_1]
                                      · have p1137_0 := h1137c.1
                                        have p1137_1 := h1137c.2.1
                                        have p1137_2 := h1137c.2.2.1
                                        have p1137_3 := h1137c.2.2.2
                                        linarith only [hlam, p1137_0]
                                    · linarith only [h1124, h1136, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h0, h1129, h1132, h1135, h879, h882, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                                · linarith only [h1, h1125, h1132, h1134, h878, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                              · linarith only [h1, h1125, h1127, h1129, h1133, h878, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1124, h1127, h1129, h1132, h878, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h1, h1129, h1131, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1130, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h1121, h1129, h882, hc12, hlam, hphi, ht23, ht34, u4elo2]
                · linarith only [h1121, h1124, h882, hlam]
              · linarith only [h0, h1, h1121, h1123, hlam]
            · linarith only [h1, h1122, h878, hc14, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1184 | h1184
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1185 | h1185
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1186 | h1186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1187 | h1187
                  · linarith only [h0, h1187, h880, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1189 | h1189
                    · linarith only [h0, h1189, h882, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1191 | h1191
                      · linarith only [h0, h1121, h1191, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1193 | h1193
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1194 | h1194
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1195 | h1195
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1196 | h1196
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1197 | h1197
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1198 | h1198
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1199 | h1199
                                    · rcases h0bigk with h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c | h1200c
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1, h1187, hc02, hc23, hlam, hphi, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, h1, h1121, h1186, h1187, hc12, hc23, hlam, hphi, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, h1, h1121, h1187, hc12, hc23, hlam, hphi, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h880, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h882, hlam, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1121, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1200_1, u0elo2]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        rcases p1200_3 (m.d 0 1) (by simp) with h1212 | h1212
                                        · linarith only [h1, h1212, hlam]
                                        · linarith only [h0, h1212, hlam]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1193, h1199, h878, hc45, hlam, hphi, ht0b, ht5b, p1200_1, u0elo2]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        rcases p1200_3 (m.d 0 1) (by simp) with h1217 | h1217
                                        · linarith only [h1, h1217, hlam]
                                        · linarith only [h1217, h879, hlam]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h878, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1200_1, u4elo0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1184, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, h1121, h882, hc12, hlam, hphi, ht23, ht34, p1200_1, u4elo2]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h879, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h0, h1, h1187, h879, hc12, hc23, hlam, hphi, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1185, hlam, p1200_0]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [h1186, hlam, p1200_1]
                                      · have p1200_0 := h1200c.1
                                        have p1200_1 := h1200c.2.1
                                        have p1200_2 := h1200c.2.2.1
                                        have p1200_3 := h1200c.2.2.2
                                        linarith only [hlam, p1200_0]
                                    · linarith only [h1186, h1199, h882, hc34, hlam, hphi, u4elo2]
                                  · linarith only [h1, h1187, h1195, h1198, h878, h882, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h1, h1187, h1197, hc12, hc35, hlam, hphi, ht23]
                              · linarith only [h1, h1187, h1195, h1196, h878, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1186, h1193, h1195, h882, hc34, hlam, hphi, u4elo2]
                          · linarith only [h0, h1, h1194, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1189, h1193, h878, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1237 | h1237
                  · linarith only [h0, h1237, h880, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1239 | h1239
                    · linarith only [h0, h1186, h1239, h882, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1241 | h1241
                      · linarith only [h0, h1121, h1241, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1243 | h1243
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1244 | h1244
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1245 | h1245
                            · linarith only [h1186, h1245, h878, h882, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1247 | h1247
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1248 | h1248
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1249 | h1249
                                  · linarith only [h1186, h1249, hc04, hlam, hphi, u4elo2]
                                  · linarith only [h0, h1249, h882, hc12, hlam, hphi, ht23, ht34, u4elo4]
                                · linarith only [h1, h1237, h1244, h1248, h879, hlam]
                              · linarith only [h1, h1237, h1243, h1247, h878, h879, hc15, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h1, h1239, h1244, h878, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1239, h1243, h878, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h1185, h879, hlam]
            · linarith only [h1, h1184, h878, hc14, hlam, hphi, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1258 | h1258
      · linarith only [h0, h1, h1258, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1260 | h1260
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1261 | h1261
          · linarith only [h0, h1261, h879, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1263 | h1263
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1264 | h1264
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1265 | h1265
                · linarith only [h1265, h878, h879, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1267 | h1267
                  · linarith only [h0, h1258, h1267, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1269 | h1269
                    · linarith only [h0, h1265, h1269, h879, hc24, hlam, hphi, u4elo4]
                    · linarith only [h1260, h1261, h1269, hc12, hc25, hlam, hphi]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1272 | h1272
                · linarith only [h1, h1264, h1272, h878, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                  · linarith only [h0, h1, h1258, h1264, h1272, h1274, hc02, hlam, hphi, ht23, ht34, u4elo4]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1276 | h1276
                    · linarith only [h0, h1, h1264, h1272, h1276, hc24, hlam, hphi, u4elo4]
                    · linarith only [h0, h1, h1260, h1264, h1272, h1276, hc12, hlam, hphi, ht23, ht34, u4elo4]
            · linarith only [h0, h1, h1260, h1263, hc24, hlam, hphi, u4elo3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1280 | h1280
          · linarith only [h0, h1260, h1280, h879, hc12, hlam, hphi, ht23, ht34, u4elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1282 | h1282
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1283 | h1283
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1284 | h1284
                · linarith only [h1284, h878, h879, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1286 | h1286
                  · linarith only [h0, h1258, h1286, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1288 | h1288
                    · linarith only [h0, h1284, h1288, h879, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1290 | h1290
                      · linarith only [h1280, h1288, h1290, h878, h879, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1292 | h1292
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1293 | h1293
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1294 | h1294
                            · linarith only [h1284, h1294, h878, h879, hlam]
                            · linarith only [h1288, h1294, h878, h879, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h1, h1283, h1293, hlam]
                        · linarith only [h1, h1288, h1292, h878, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
                · linarith only [h1299, h878, h879, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1301 | h1301
                  · linarith only [h0, h1, h1258, h1260, h1301, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1303 | h1303
                    · linarith only [h0, h1260, h1299, h1303, hc24, hlam, hphi, u4elo4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1305 | h1305
                      · linarith only [h1, h1280, h1283, h1303, h1305, h878, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1307 | h1307
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1308 | h1308
                          · linarith only [h0, h1, h1283, h1301, h1308, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h1303, h1308, h878, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1303, h1307, h878, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1282, h878, hc14, hlam, hphi, u4elo3]
  · linarith only [h0, h878, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0_x0 m hb0 hb1 hb3 hb4 h0 h1
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x0_x1 m hb0 hb1 hb3 hb4 h0 h1

end R2N4
