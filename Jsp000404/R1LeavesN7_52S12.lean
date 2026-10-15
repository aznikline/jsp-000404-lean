import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h890 | h890
  · rcases m.htr 0 1 5 (by decide) (by decide) with h891 | h891
    · rcases m.htr 0 2 3 (by decide) (by decide) with h892 | h892
      · linarith only [h0, h1, h892, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h894 | h894
        · rcases m.htr 0 2 5 (by decide) (by decide) with h895 | h895
          · rcases m.htr 0 3 4 (by decide) (by decide) with h896 | h896
            · rcases m.htr 0 3 5 (by decide) (by decide) with h897 | h897
              · rcases m.htr 0 4 5 (by decide) (by decide) with h898 | h898
                · rcases m.htr 1 2 3 (by decide) (by decide) with h899 | h899
                  · linarith only [h0, h1, h892, h899, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h901 | h901
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h902 | h902
                      · linarith only [h0, h1, h899, h902, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h895, h899, h902, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h894, h899, h901, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h906 | h906
                  · linarith only [h0, h1, h906, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h908 | h908
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h909 | h909
                      · linarith only [h0, h1, h906, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h895, h906, h909, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h894, h906, h908, hc12, hc23, hlam, hphi]
              · linarith only [h896, h897, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h890, h896, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h915 | h915
            · rcases m.htr 0 3 5 (by decide) (by decide) with h916 | h916
              · rcases m.htr 0 4 5 (by decide) (by decide) with h917 | h917
                · linarith only [h894, h895, h917, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                  · linarith only [h0, h1, h919, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h921 | h921
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h922 | h922
                      · linarith only [h0, h894, h895, h915, h922, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h926 | h926
                            · linarith only [h1, h891, h919, h921, h922, h926, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h890, h891, h919, h924, h926, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · linarith only [h1, h891, h922, h925, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h891, h916, h924, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1, h891, h894, h895, h919, h921, hc12, hc23, hlam, hphi]
              · linarith only [h915, h916, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h891, h894, h895, h915, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h934 | h934
          · rcases m.htr 0 3 4 (by decide) (by decide) with h935 | h935
            · rcases m.htr 0 3 5 (by decide) (by decide) with h936 | h936
              · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
                · rcases m.htr 1 2 3 (by decide) (by decide) with h938 | h938
                  · linarith only [h0, h1, h892, h938, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
                    · linarith only [h0, h1, h894, h934, h938, h940, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h942 | h942
                      · linarith only [h1, h890, h938, h940, h942, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h894, h934, h942, hc12, hc24, hlam, hphi]
                · linarith only [h894, h934, h937, hlam]
              · linarith only [h935, h936, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h890, h935, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h948 | h948
            · rcases m.htr 0 3 5 (by decide) (by decide) with h949 | h949
              · rcases m.htr 0 4 5 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
                  · linarith only [h0, h1, h892, h951, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h953 | h953
                    · linarith only [h0, h1, h894, h950, h953, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h955 | h955
                      · linarith only [h0, h934, h955, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h957 | h957
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h958 | h958
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h959 | h959
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h960 | h960
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h961 | h961
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h962 | h962
                                  · linarith only [h1, h890, h951, h957, h962, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                  · linarith only [h1, h890, h950, h951, h962, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h890, h894, h950, h951, h961, hc02, hc23, hlam, hphi]
                              · linarith only [h0, h1, h951, h960, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h891, h951, h958, h959, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1, h890, h953, h958, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h890, h948, h950, h957, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h970 | h970
                  · linarith only [h0, h1, h892, h970, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h972 | h972
                    · linarith only [h0, h894, h972, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h974 | h974
                      · linarith only [h0, h934, h974, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h976 | h976
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h977 | h977
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h978 | h978
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h979 | h979
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h980 | h980
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h981 | h981
                                  · linarith only [h890, h950, h976, h981, hlam]
                                  · rcases h0bigk with h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c | h983c
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h970, hc02, hc23, hlam, hphi, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h970, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h970, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u5ehi0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h0, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h892, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h894, hlam, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h934, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h0, h1, h970, hc12, hc23, hlam, hphi, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h890, h970, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p983_1, u3ehi3]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h891, h970, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p983_1, u5ehi1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h890, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h0, h1, h890, h970, hc12, hc23, hlam, hphi, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h948, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h950, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h891, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h0, h1, h891, h970, hc12, hc23, hlam, hphi, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h949, hlam, p983_0]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [h1, h891, h970, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p983_1]
                                    · have p983_0 := h983c.1
                                      have p983_1 := h983c.2.1
                                      have p983_2 := h983c.2.2.1
                                      have p983_3 := h983c.2.2.2
                                      linarith only [hlam, p983_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1009 | h1009
                                  · linarith only [h1, h1009, h890, h970, h976, h980, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                  · rcases h0bigk with h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c | h1011c
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, h1, h970, hc12, hc23, hlam, hphi, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, h970, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, h970, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1011_1, u5ehi0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h892, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h894, hlam, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h934, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, h970, hc01, hc23, hlam, hphi, ht12, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, h1, h970, hc12, hc23, hlam, hphi, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, h1, h894, h970, hc12, hc23, hlam, hphi, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, h1009, h891, h970, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1011_1, u3ehi3]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h890, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, h1, h890, h970, hc12, hc23, hlam, hphi, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h948, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h950, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h891, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h0, h1, h891, h970, hc12, hc23, hlam, hphi, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h949, hlam, p1011_0]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [h1, h891, h970, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1011_1]
                                    · have p1011_0 := h1011c.1
                                      have p1011_1 := h1011c.2.1
                                      have p1011_2 := h1011c.2.2.1
                                      have p1011_3 := h1011c.2.2.2
                                      linarith only [hlam, p1011_0]
                              · linarith only [h0, h1, h970, h979, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h890, h970, h976, h978, hlam]
                          · linarith only [h1, h890, h976, h977, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1, h891, h976, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
              · linarith only [h948, h949, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h890, h948, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1043 | h1043
      · linarith only [h0, h1, h1043, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1045 | h1045
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1046 | h1046
          · linarith only [h0, h1046, h891, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1048 | h1048
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1049 | h1049
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1050 | h1050
                · linarith only [h0, h1045, h1050, h891, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1052 | h1052
                  · linarith only [h0, h1, h1043, h1052, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1054 | h1054
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1055 | h1055
                      · linarith only [h0, h1046, h1055, h891, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1057 | h1057
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1058 | h1058
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1059 | h1059
                            · linarith only [h0, h1052, h1054, h1058, h1059, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1052, h1054, h1057, h1058, h1059, h890, h891, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h0, h1, h1049, h1054, h1057, h1058, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h1054, h1057, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h1043, h1045, h1054, hc12, hc23, hlam, hphi]
              · linarith only [h1048, h1049, hc35, hlam, hphi, u3ehi3]
            · linarith only [h0, h1, h1045, h1048, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1067 | h1067
          · linarith only [h1045, h1067, h890, h891, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1069 | h1069
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1070 | h1070
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
                · linarith only [h1071, h890, h891, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
                  · linarith only [h0, h1, h1043, h1073, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1075 | h1075
                    · linarith only [h0, h1045, h1075, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1077 | h1077
                      · linarith only [h0, h1067, h1077, h891, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1079 | h1079
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1080 | h1080
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1081 | h1081
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1082 | h1082
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1083 | h1083
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1084 | h1084
                                  · linarith only [h1045, h1071, h1079, h1080, h1084, h890, h891, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c | h1086c
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, h1071, h1081, h1083, h891, hc12, hc23, hlam, hphi, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1071, h1079, h1081, h1083, h890, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1086_1, u3ehi3]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h891, hlam, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1043, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1045, hlam, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1067, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, h1043, hc12, hc23, hlam, hphi, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1043, h1079, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1086_1, u3ehi3]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1043, h1079, h890, h891, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1086_1, u3ehi3]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h890, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, h890, h891, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1069, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1071, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1071, h1083, hc01, hc24, hlam, hphi, ht12, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h0, h1071, h1083, hc12, hc24, hlam, hphi, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1070, hlam, p1086_0]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [h1071, h1083, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1086_1]
                                    · have p1086_0 := h1086c.1
                                      have p1086_1 := h1086c.2.1
                                      have p1086_2 := h1086c.2.2.1
                                      have p1086_3 := h1086c.2.2.2
                                      linarith only [hlam, p1086_0]
                                · linarith only [h1077, h1079, h1083, h890, h891, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h1, h1043, h1079, h1082, h890, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1073, h1079, h1080, h1081, h890, h891, hlam]
                          · linarith only [h1, h1070, h1080, h890, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1, h1070, h1079, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1069, h1070, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1069, h890, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1119 | h1119
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1120 | h1120
      · linarith only [h0, h1, h1120, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1122 | h1122
        · linarith only [h0, h1122, h890, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1124 | h1124
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1125 | h1125
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1126 | h1126
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1127 | h1127
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1128 | h1128
                  · linarith only [h1120, h1124, h1128, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1130 | h1130
                    · linarith only [h0, h1122, h1124, h1130, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1132 | h1132
                      · linarith only [h0, h1, h1128, h1132, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h1, h1124, h1128, h1132, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1124, h1127, h890, hlam]
              · linarith only [h1125, h1126, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1137 | h1137
              · linarith only [h1125, h1137, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1, h1124, h1137, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1140 | h1140
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1141 | h1141
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
                  · linarith only [h0, h1, h1120, h1143, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1145 | h1145
                    · linarith only [h0, h1122, h1145, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1147 | h1147
                      · linarith only [h0, h1, h1124, h1143, h1147, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1151 | h1151
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1152 | h1152
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1153 | h1153
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1154 | h1154
                                  · rcases h0bigk with h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c | h1155c
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1143, h1149, h890, hc02, hc23, hlam, hphi, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h890, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1143, h1149, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1155_1, u5ehi0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1120, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1122, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1124, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1119, hc03, hlam, hphi, ht0b, ht5b, p1155_1, u5ehi1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1, h1143, hc12, hc23, hlam, hphi, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1, h1119, h1143, h1150, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1155_1, u3ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1, h1119, h1143, h1150, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1155_1, u3ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1119, h1150, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1155_1, u3ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1143, h1149, h890, hc12, hc23, hlam, hphi, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1140, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1119, h1143, h1149, h1150, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1155_1, u3ehi4]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1119, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h0, h1, h1119, h1143, hc12, hc23, hlam, hphi, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1141, hlam, p1155_0]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [h1142, hlam, p1155_1]
                                    · have p1155_0 := h1155c.1
                                      have p1155_1 := h1155c.2.1
                                      have p1155_2 := h1155c.2.2.1
                                      have p1155_3 := h1155c.2.2.2
                                      linarith only [hlam, p1155_0]
                                  · rcases h0bigk with h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c | h1181c
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h0, h1143, h1149, h890, hc12, hc23, hlam, hphi, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h890, hlam, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1142, h1143, h1149, h1154, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1181_1, u3ehi3]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h0, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1120, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1122, hlam, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1124, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1, h1143, hc01, hc23, hlam, hphi, ht12, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h0, h1, h1143, hc12, hc23, hlam, hphi, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1, h1119, h1143, h1150, h1154, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1181_1, u3ehi3]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1, h1142, h1143, h1154, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1181_1, u3ehi3]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1119, h1150, h1154, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1181_1, u3ehi3]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h0, h1143, h1149, h890, hc12, hc23, hlam, hphi, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1140, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1142, h1143, h1149, h1154, h890, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1181_1, u3ehi3]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1119, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h0, h1124, hc12, hc25, hlam, hphi, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1141, hlam, p1181_0]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [h1142, hlam, p1181_1]
                                    · have p1181_0 := h1181c.1
                                      have p1181_1 := h1181c.2.1
                                      have p1181_2 := h1181c.2.2.1
                                      have p1181_3 := h1181c.2.2.2
                                      linarith only [hlam, p1181_0]
                                · linarith only [h0, h1145, h1153, h890, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1119, h1143, h1149, h1150, h1152, h890, hlam]
                            · linarith only [h1119, h1143, h1149, h1150, h1151, h890, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h1119, h1149, h1150, h890, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                        · linarith only [h1, h1140, h1149, hlam]
                · linarith only [h1119, h1142, h890, hlam]
              · linarith only [h1140, h1141, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1214 | h1214
              · linarith only [h1140, h1214, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1, h1119, h1214, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1217 | h1217
      · linarith only [h0, h1, h1217, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1219 | h1219
        · linarith only [h0, h1219, h890, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1221 | h1221
          · linarith only [h0, h1119, h1221, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1223 | h1223
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1224 | h1224
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1225 | h1225
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
                  · linarith only [h0, h1217, h1226, h890, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
                    · linarith only [h0, h1119, h1219, h1225, h1228, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                      · linarith only [h0, h1119, h1221, h1230, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1234 | h1234
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1235 | h1235
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1237 | h1237
                                  · rcases h0bigk with h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c | h1238c
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1119, h1230, h1234, h1236, hc02, hc23, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h890, hlam, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1119, hlam, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1217, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1219, hlam, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1221, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, h1217, hc12, hc23, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, h1217, h890, hc12, hc23, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, h1119, h1217, hc12, hc23, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, h1219, hc12, hc24, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1223, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1217, h1223, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1238_1, u5ehi0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h0, h1119, h1230, hc12, hc25, hlam, hphi, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1224, hlam, p1238_0]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [h1225, hlam, p1238_1]
                                    · have p1238_0 := h1238c.1
                                      have p1238_1 := h1238c.2.1
                                      have p1238_2 := h1238c.2.2.1
                                      have p1238_3 := h1238c.2.2.2
                                      linarith only [hlam, p1238_0]
                                  · rcases h0bigk with h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c | h1264c
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1, h1226, hc12, hc23, hlam, hphi, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h890, hlam, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1119, hlam, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1217, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1219, hlam, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1221, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1, h1226, hc01, hc23, hlam, hphi, ht12, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1, h1226, hc12, hc23, hlam, hphi, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1, h1225, h1226, h1237, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1264_1, u3ehi3]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1, h1226, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1264_1, u5ehi0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1226, h1232, h890, hc12, hc23, hlam, hphi, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1223, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1119, h1226, h1232, h890, hc12, hc23, hlam, hphi, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1225, h1226, h1232, h1237, h890, hc05, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1264_1, u3ehi3]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h0, h1119, h1230, h1234, h1236, hc12, hc23, hlam, hphi, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1224, hlam, p1264_0]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [h1225, hlam, p1264_1]
                                    · have p1264_0 := h1264c.1
                                      have p1264_1 := h1264c.2.1
                                      have p1264_2 := h1264c.2.2.1
                                      have p1264_3 := h1264c.2.2.2
                                      linarith only [hlam, p1264_0]
                                · linarith only [h0, h1219, h1225, h1226, h1232, h1236, h890, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1, h1226, h1235, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1226, h1232, h1234, h890, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h1, h1224, h1233, hlam]
                        · linarith only [h1, h1223, h1232, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1295 | h1295
                  · linarith only [h0, h1295, h890, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1297 | h1297
                    · linarith only [h0, h1219, h1225, h1297, h890, hc02, hc45, hlam, hphi, ht23, ht34]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1299 | h1299
                      · linarith only [h0, h1299, h890, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1301 | h1301
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1303 | h1303
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1304 | h1304
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1305 | h1305
                                · linarith only [h0, h1225, h1303, h1305, h890, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h1297, h1305, h890, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1, h1224, h1295, h1304, hlam]
                            · linarith only [h1, h1224, h1295, h1303, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h0, h1224, h1301, h1302, h890, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h1223, h1225, h1301, hc45, hlam, hphi, ht34, u3ehi0]
              · linarith only [h1223, h1224, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1313 | h1313
              · linarith only [h1223, h1313, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1315 | h1315
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
                  · linarith only [h0, h1, h1316, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1318 | h1318
                    · linarith only [h0, h1219, h1318, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1320 | h1320
                      · linarith only [h0, h1, h1223, h1320, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1322 | h1322
                        · linarith only [h0, h1, h1223, h1316, h1322, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1322, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1325 | h1325
                  · linarith only [h0, h1, h1325, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1327 | h1327
                    · linarith only [h0, h1, h1223, h1315, h1327, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
                      · linarith only [h0, h1, h1223, h1315, h1329, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1331 | h1331
                        · linarith only [h0, h1, h1223, h1325, h1331, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h1331, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1334 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1335 | h1335
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1336 | h1336
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1337 | h1337
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1338 | h1338
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1339 | h1339
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1340 | h1340
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1341 | h1341
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1342 | h1342
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1343 | h1343
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1344 | h1344
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1345 | h1345
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1346 | h1346
                        · linarith only [h0, h1334, h1346, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1334, h1340, h1343, h1346, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1336, h1345, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1336, h1344, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h0, h1334, h1343, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1352 | h1352
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1353 | h1353
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1354 | h1354
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1355 | h1355
                        · linarith only [h0, h1334, h1355, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1334, h1340, h1352, h1355, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1334, h1352, h1354, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1334, h1352, h1353, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1340, h1352, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1340, h1341, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1362 | h1362
              · linarith only [h1340, h1362, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                        · linarith only [h1334, h1340, h1368, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1370 | h1370
                          · linarith only [h0, h1334, h1370, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1372 | h1372
                            · linarith only [h0, h1337, h1340, h1372, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1374 | h1374
                              · linarith only [h1334, h1362, h1365, h1374, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1376 | h1376
                                · linarith only [h0, h1335, h1366, h1376, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                                · linarith only [h0, h1335, h1364, h1372, h1376, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1336, h1367, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1334, h1365, h1366, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1365, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1382 | h1382
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1383 | h1383
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1384 | h1384
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1385 | h1385
                        · linarith only [h1334, h1340, h1385, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1387 | h1387
                          · linarith only [h1334, h1362, h1387, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1389 | h1389
                            · linarith only [h1334, h1340, h1382, h1389, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1391 | h1391
                              · linarith only [h1334, h1362, h1382, h1391, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1393 | h1393
                                · linarith only [h0, h1335, h1364, h1383, h1393, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1395 | h1395
                                  · linarith only [h1335, h1364, h1385, h1395, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h1340, h1395, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h0, h1336, h1384, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1334, h1382, h1383, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1382, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1336, h1339, hlam]
        · linarith only [h0, h1335, h1338, hlam]
      · linarith only [h0, h1334, h1337, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1404 | h1404
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1405 | h1405
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1406 | h1406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1407 | h1407
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1408 | h1408
              · linarith only [h1334, h1336, h1408, hlam]
              · linarith only [h1407, h1408, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1411 | h1411
              · linarith only [h1407, h1411, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1413 | h1413
                · linarith only [h1335, h1336, h1413, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1415 | h1415
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1418 | h1418
                        · linarith only [h1334, h1336, h1417, h1418, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1420 | h1420
                          · linarith only [h1335, h1336, h1417, h1418, h1420, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                          · linarith only [h1335, h1336, h1418, h1420, hc35, hlam, hphi, u3ehi1]
                      · linarith only [h0, h1406, h1417, hlam]
                    · linarith only [h0, h1334, h1415, h1416, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1415, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1427 | h1427
              · linarith only [h1334, h1336, h1427, hlam]
              · linarith only [h1426, h1427, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1430 | h1430
              · linarith only [h1426, h1430, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1432 | h1432
                · linarith only [h0, h1335, h1406, h1432, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1434 | h1434
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1435 | h1435
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1436 | h1436
                      · linarith only [h0, h1334, h1406, h1434, h1436, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h0, h1334, h1434, h1436, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1334, h1434, h1435, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h1335, h1405, hlam]
      · linarith only [h0, h1334, h1404, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1443 | h1443
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1444 | h1444
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1445 | h1445
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1446 | h1446
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1447 | h1447
            · linarith only [h1334, h1335, h1447, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1449 | h1449
              · linarith only [h1447, h1449, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1451 | h1451
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1452 | h1452
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1453 | h1453
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1454 | h1454
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1455 | h1455
                        · linarith only [h1334, h1447, h1455, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1334, h1335, h1452, h1455, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1335, h1443, h1453, h1454, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                    · linarith only [h0, h1445, h1453, hlam]
                  · linarith only [h0, h1334, h1452, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1334, h1335, h1451, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1443, h1446, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1463 | h1463
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1464 | h1464
            · linarith only [h0, h1334, h1445, h1464, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1466 | h1466
              · linarith only [h1464, h1466, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1469 | h1469
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1470 | h1470
                    · linarith only [h0, h1334, h1445, h1470, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1334, h1469, h1470, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1469, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1334, h1445, h1468, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h1443, h1463, hlam]
      · linarith only [h0, h1334, h1444, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1477 | h1477
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1478 | h1478
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1479 | h1479
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1480 | h1480
            · linarith only [h1334, h1335, h1480, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1482 | h1482
              · linarith only [h1480, h1482, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1484 | h1484
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1485 | h1485
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1486 | h1486
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1487 | h1487
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1488 | h1488
                        · linarith only [h1334, h1335, h1480, h1486, h1488, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1334, h1335, h1485, h1488, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h1334, h1335, h1479, h1485, h1486, h1487, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1334, h1485, h1486, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1485, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1334, h1335, h1484, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1495 | h1495
            · linarith only [h1334, h1335, h1495, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1497 | h1497
              · linarith only [h1495, h1497, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1499 | h1499
                · linarith only [h1478, h1479, h1499, hlam]
                · linarith only [h1334, h1335, h1499, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1502 | h1502
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1503 | h1503
            · linarith only [h0, h1334, h1478, h1503, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1505 | h1505
              · linarith only [h1503, h1505, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                    · linarith only [h1334, h1443, h1478, h1502, h1509, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1334, h1508, h1509, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1508, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1334, h1335, h1507, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1514 | h1514
            · linarith only [h0, h1334, h1478, h1514, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1516 | h1516
              · linarith only [h1514, h1516, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1518 | h1518
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1519 | h1519
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1520 | h1520
                    · linarith only [h0, h1334, h1478, h1519, h1520, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h1334, h1519, h1520, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1334, h1519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h1334, h1335, h1518, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1334, h1477, hlam]

set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1334 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1526 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1527 | h1527
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1528 | h1528
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1529 | h1529
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1530 | h1530
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1531 | h1531
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1532 | h1532
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1533 | h1533
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1534 | h1534
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1535 | h1535
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1536 | h1536
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1537 | h1537
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1538 | h1538
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1539 | h1539
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1540 | h1540
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1541 | h1541
                              · linarith only [h1334, h1526, h1534, h1535, h1541, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                              · linarith only [h1334, h1526, h1533, h1534, h1539, h1541, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1334, h1527, h1534, h1538, h1540, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h1334, h1526, h1534, h1537, h1539, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1334, h1527, h1538, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h1334, h1527, h1537, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h1334, h1526, h1533, h1534, h1536, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h1334, h1526, h1533, h1534, h1535, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h1526, h1533, h1534, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1551 | h1551
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1552 | h1552
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1553 | h1553
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1554 | h1554
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1555 | h1555
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1557 | h1557
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1558 | h1558
                              · linarith only [h1526, h1533, h1552, h1558, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1560 | h1560
                                · linarith only [h1528, h1533, h1556, h1560, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h0, hlam, p1562_1]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1334, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1334, h1526, h1551, h1552, h1556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1334, h1551, hc12, hlam, hphi, ht01, ht0b, ht5b, p1562_1, u5ehi0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1562_1]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h0, h1334, h1526, h1552, h1556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h0, h1526, h1552, h1556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h0, h1527, h1553, h1557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi4]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1526, h1552, h1556, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1528, hlam, p1562_1]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1334, h1526, h1551, h1552, h1556, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1334, h1527, h1551, h1553, h1557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi4]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1526, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1529, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1531, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1533, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1527, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1530, hlam, p1562_1]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1532, hlam, p1562_0]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [h1526, h1552, h1556, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1562_1, u3ehi3]
                                  · have p1562_0 := h1562c.1
                                    have p1562_1 := h1562c.2.1
                                    have p1562_2 := h1562c.2.2.1
                                    have p1562_3 := h1562c.2.2.2
                                    linarith only [hlam, p1562_0]
                            · linarith only [h0, h1527, h1555, h1557, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h1531, h1533, h1556, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h1334, h1527, h1555, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                      · linarith only [h1334, h1527, h1554, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                    · linarith only [h1334, h1527, h1551, h1553, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                  · linarith only [h1334, h1527, h1551, h1552, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1527, h1551, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1531, h1532, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1334, h1526, h1531, hlam]
        · linarith only [h1334, h1527, h1528, h1530, hlam]
      · linarith only [h1334, h1526, h1528, h1529, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1599 | h1599
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1600 | h1600
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1601 | h1601
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1602 | h1602
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1603 | h1603
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1604 | h1604
                · linarith only [h1528, h1600, h1604, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1526, h1603, h1604, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1607 | h1607
                · linarith only [h0, h1527, h1528, h1607, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h1527, h1607, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · linarith only [h1601, h1602, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1334, h1526, h1601, hlam]
        · linarith only [h0, h1527, h1600, hlam]
      · linarith only [h0, h1526, h1599, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1614 | h1614
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1615 | h1615
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1616 | h1616
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1617 | h1617
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1618 | h1618
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1619 | h1619
              · linarith only [h1526, h1527, h1619, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1621 | h1621
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1622 | h1622
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1623 | h1623
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1624 | h1624
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                              · linarith only [h1526, h1527, h1619, h1621, h1622, h1625, h1628, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1630 | h1630
                                · linarith only [h1526, h1527, h1619, h1622, h1626, h1630, hlam]
                                · rcases h0bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1334, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1526, h1527, h1621, h1622, h1625, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1527, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1334, h1526, h1622, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1526, h1622, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h0, h1526, h1527, h1622, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1526, h1622, h1626, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1614, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1334, h1526, h1621, h1622, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1334, h1526, h1527, h1621, h1622, h1626, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1526, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1615, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1617, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1619, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1526, h1622, h1626, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1616, hlam, p1632_1]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1618, hlam, p1632_0]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [h1526, h1619, h1622, h1626, hc45, hlam, hphi, ht34, p1632_1, u3ehi3]
                                  · have p1632_0 := h1632c.1
                                    have p1632_1 := h1632c.2.1
                                    have p1632_2 := h1632c.2.2.1
                                    have p1632_3 := h1632c.2.2.2
                                    linarith only [hlam, p1632_0]
                            · linarith only [h1334, h1618, h1621, h1626, h1627, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1617, h1619, h1626, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h1334, h1618, h1625, hlam]
                      · linarith only [h1334, h1618, h1624, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h0, h1616, h1623, hlam]
                  · linarith only [h0, h1615, h1622, hlam]
                · linarith only [h0, h1614, h1621, hlam]
            · linarith only [h1617, h1618, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1334, h1526, h1617, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1667 | h1667
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1668 | h1668
            · linarith only [h1614, h1616, h1668, hlam]
            · linarith only [h1667, h1668, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1334, h1526, h1667, hlam]
      · linarith only [h0, h1526, h1615, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1673 | h1673
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1674 | h1674
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1675 | h1675
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1676 | h1676
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1677 | h1677
              · linarith only [h1526, h1527, h1677, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1679 | h1679
                · linarith only [h1614, h1674, h1679, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1681 | h1681
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1682 | h1682
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1683 | h1683
                      · linarith only [h1526, h1527, h1679, h1682, h1683, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1526, h1527, h1675, h1679, h1682, h1683, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1526, h1674, h1675, h1682, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1673, h1681, hlam]
            · linarith only [h1675, h1676, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1526, h1614, h1675, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1690 | h1690
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1691 | h1691
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1692 | h1692
              · linarith only [h0, h1526, h1674, h1692, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1694 | h1694
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1695 | h1695
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1696 | h1696
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1697 | h1697
                      · linarith only [h0, h1526, h1614, h1694, h1697, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1334, h1526, h1690, h1697, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1526, h1614, h1690, h1694, h1696, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1526, h1614, h1690, h1694, h1695, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1702 | h1702
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1703 | h1703
                    · linarith only [h0, h1526, h1674, h1690, h1694, h1703, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1705 | h1705
                      · linarith only [h0, h1526, h1694, h1705, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1334, h1690, h1692, h1705, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h0, h1526, h1673, h1674, h1702, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1690, h1691, hc35, hlam, hphi, u3ehi3]
          · linarith only [h0, h1526, h1614, h1690, hlam]
      · linarith only [h0, h1526, h1673, hlam]

end R2N4
