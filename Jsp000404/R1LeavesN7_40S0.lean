import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h928 | h928
  · rcases m.htr 0 2 3 (by decide) (by decide) with h929 | h929
    · rcases m.htr 0 2 4 (by decide) (by decide) with h930 | h930
      · rcases m.htr 0 2 5 (by decide) (by decide) with h931 | h931
        · rcases m.htr 0 3 4 (by decide) (by decide) with h932 | h932
          · rcases m.htr 0 3 5 (by decide) (by decide) with h933 | h933
            · rcases m.htr 0 4 5 (by decide) (by decide) with h934 | h934
              · rcases m.htr 1 2 3 (by decide) (by decide) with h935 | h935
                · rcases m.htr 1 2 4 (by decide) (by decide) with h936 | h936
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h937 | h937
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h938 | h938
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h939 | h939
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h940 | h940
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h941 | h941
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h942 | h942
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h943 | h943
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h944 | h944
                                  · linarith only [h0, h927, h935, h941, h944, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h927, h938, h940, h944, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h927, h938, h940, h943, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h927, h933, h942, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h927, h932, h941, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h927, h932, h934, h936, h940, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h927, h933, h938, h939, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h927, h932, h935, h938, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h927, h935, h937, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h927, h931, h932, h934, h936, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h927, h931, h932, h934, h935, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h956 | h956
                · rcases m.htr 1 2 4 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h960 | h960
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h961 | h961
                          · linarith only [h0, h927, h934, h959, h961, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h963 | h963
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h964 | h964
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h965 | h965
                                · linarith only [h930, h934, h965, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h967 | h967
                                  · linarith only [h930, h934, h967, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h1bigk with h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c | h969c
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h956, h964, h965, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h957, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h958, h965, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h927, h956, h964, h965, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      rcases p969_3 (m.d 0 1) (by simp) with h977 | h977
                                      · linarith only [h0, h977, hlam]
                                      · linarith only [h927, h977, hlam]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      rcases p969_3 (m.d 0 1) (by simp) with h980 | h980
                                      · linarith only [h0, h980, hlam]
                                      · linarith only [h927, h956, h964, h965, h980, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      rcases p969_3 (m.d 0 1) (by simp) with h983 | h983
                                      · linarith only [h0, h983, hlam]
                                      · linarith only [h928, h983, hlam]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h927, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h956, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h927, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p969_1]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h927, h958, h965, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h928, h958, h965, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p969_1, u2ehi3]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h957, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h959, hlam, p969_1]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h961, hlam, p969_1]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h928, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h958, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h960, hlam, p969_0]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [h0, h928, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p969_1]
                                    · have p969_0 := h969c.1
                                      have p969_1 := h969c.2.1
                                      have p969_2 := h969c.2.2.1
                                      have p969_3 := h969c.2.2.2
                                      linarith only [hlam, p969_0]
                              · linarith only [h0, h927, h933, h964, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h927, h932, h963, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h927, h933, h959, h960, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h927, h932, h956, h959, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h927, h956, h958, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h927, h930, h933, h934, h956, h957, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h927, h931, h933, h956, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1008 | h1008
              · linarith only [h1008, h932, h933, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1011 | h1011
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                        · linarith only [h1014, h927, h933, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1016 | h1016
                          · linarith only [h0, h1008, h1013, h1014, h1016, h928, h930, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1018 | h1018
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1019 | h1019
                              · linarith only [h1010, h1019, h927, h933, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1021 | h1021
                                · linarith only [h1008, h1021, h930, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1023 | h1023
                                  · linarith only [h0, h1008, h1010, h1014, h1018, h1023, h928, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, h1010, h1018, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, h1011, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1, u2ehi3]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, h1011, h1013, h1014, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1, u2ehi3]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1011, h1013, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1, u2ehi3]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      rcases p1025_3 (m.d 0 1) (by simp) with h1033 | h1033
                                      · linarith only [h0, h1033, hlam]
                                      · linarith only [h1033, h927, hlam]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      rcases p1025_3 (m.d 0 1) (by simp) with h1036 | h1036
                                      · linarith only [h0, h1036, hlam]
                                      · linarith only [h1013, h1014, h1036, h928, hlam]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      rcases p1025_3 (m.d 0 1) (by simp) with h1039 | h1039
                                      · linarith only [h0, h1039, hlam]
                                      · linarith only [h1039, h928, hlam]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h927, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1010, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1011, h1014, h928, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1025_1, u2ehi3]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1014, hlam, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1012, h928, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1025_1, u2ehi4]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1011, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1013, hlam, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1016, hlam, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h928, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h1012, hlam, p1025_0]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, h928, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [h0, h928, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1025_1]
                                    · have p1025_0 := h1025c.1
                                      have p1025_1 := h1025c.2.1
                                      have p1025_2 := h1025c.2.2.1
                                      have p1025_3 := h1025c.2.2.2
                                      linarith only [hlam, p1025_0]
                            · linarith only [h1018, h932, h933, hc23, hc35, hlam, hphi]
                      · linarith only [h1010, h1013, h932, h933, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1010, h1012, h927, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1010, h1011, h927, h930, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1010, h927, h930, h932, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1062 | h1062
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1063 | h1063
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1064 | h1064
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1065 | h1065
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1066 | h1066
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1067 | h1067
                      · linarith only [h0, h1062, h1066, h1067, h927, h928, h932, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1069 | h1069
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1070 | h1070
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1071 | h1071
                            · linarith only [h1064, h1071, h927, h932, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1073 | h1073
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1074 | h1074
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1075 | h1075
                                  · rcases h1bigk with h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c | h1076c
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h0, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h0, h1064, h1073, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1076_1]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h0, h1066, h1067, h1069, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h0, h1066, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1066, h1069, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      rcases p1076_3 (m.d 0 1) (by simp) with h1084 | h1084
                                      · linarith only [h0, h1084, hlam]
                                      · linarith only [h1084, h927, hlam]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      rcases p1076_3 (m.d 0 1) (by simp) with h1087 | h1087
                                      · linarith only [h0, h1087, hlam]
                                      · linarith only [h1066, h1069, h1087, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      rcases p1076_3 (m.d 0 1) (by simp) with h1090 | h1090
                                      · linarith only [h0, h1090, hlam]
                                      · linarith only [h1090, h928, hlam]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h927, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1064, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1067, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1066, h927, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1067, h927, hc13, hc34, hlam, hphi, p1076_1]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1065, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1064, h1067, h1073, hc34, hlam, hphi, ht23, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1066, h1067, hc34, hlam, hphi, ht23, p1076_1, u2ehi4]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h928, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1066, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1069, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [h1070, hlam, p1076_0]
                                    · have p1076_0 := h1076c.1
                                      have p1076_1 := h1076c.2.1
                                      have p1076_2 := h1076c.2.2.1
                                      have p1076_3 := h1076c.2.2.2
                                      linarith only [hlam, p1076_0]
                                  · linarith only [h1064, h1073, h1075, h927, h932, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · linarith only [h1063, h1071, h1073, h1074, h932, hc34, hlam, hphi, ht23, u2ehi4]
                              · linarith only [h0, h1062, h1073, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1062, h1063, h1065, h1070, h932, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1062, h1069, h932, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h1064, h1066, h927, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1064, h1065, h927, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1064, h930, hc23, hlam, hphi, u2ehi3]
              · linarith only [h1062, h1063, h932, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1117 | h1117
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1118 | h1118
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1119 | h1119
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1120 | h1120
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1121 | h1121
                      · linarith only [h1121, h927, h932, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1123 | h1123
                        · linarith only [h1062, h1123, h927, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1125 | h1125
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1126 | h1126
                            · linarith only [h1118, h1126, h927, h932, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1128 | h1128
                              · linarith only [h1062, h1118, h1128, h927, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1130 | h1130
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1131 | h1131
                                  · rcases h1bigk with h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c | h1132c
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h0, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h0, h1118, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h0, h1118, h1123, h1125, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h0, h1118, h1123, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      rcases p1132_3 (m.d 0 1) (by simp) with h1140 | h1140
                                      · linarith only [h0, h1140, hlam]
                                      · linarith only [h1140, h927, hlam]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      rcases p1132_3 (m.d 0 1) (by simp) with h1143 | h1143
                                      · linarith only [h0, h1143, hlam]
                                      · linarith only [h1118, h1123, h1143, h928, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      rcases p1132_3 (m.d 0 1) (by simp) with h1146 | h1146
                                      · linarith only [h0, h1146, hlam]
                                      · linarith only [h1146, h928, hlam]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h927, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1121, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1123, hlam, p1132_1]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, h1123, h928, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1119, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, h1121, hc34, hlam, hphi, ht23, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, h1121, h1123, hc34, hlam, hphi, ht23, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h928, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1120, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1118, h928, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1132_1, u2ehi2]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [h1125, hlam, p1132_0]
                                    · have p1132_0 := h1132c.1
                                      have p1132_1 := h1132c.2.1
                                      have p1132_2 := h1132c.2.2.1
                                      have p1132_3 := h1132c.2.2.2
                                      linarith only [hlam, p1132_0]
                                  · linarith only [h1118, h1131, h927, h932, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h1117, h1130, h932, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1117, h1119, h1125, h932, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h1118, h1120, h927, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1118, h1119, h927, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1062, h1118, h928, h929, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1170 | h1170
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1172 | h1172
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
                      · linarith only [h1173, h927, h932, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1175 | h1175
                        · linarith only [h1062, h1175, h927, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1177 | h1177
                          · linarith only [h1117, h1170, h1173, h1177, h927, h932, hc34, hlam, hphi, ht23, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1179 | h1179
                            · linarith only [h1170, h1179, h927, h932, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1181 | h1181
                              · linarith only [h1062, h1170, h1181, h927, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1183 | h1183
                                · linarith only [h1117, h1170, h1171, h1177, h1183, h927, h928, h932, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1185 | h1185
                                  · linarith only [h1117, h1170, h1185, h927, h932, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1170, h1185, h927, h932, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h1170, h1172, h927, hc25, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1170, h1171, h927, h930, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1170, h929, hlam]
        · linarith only [h930, h931, hc25, hlam, hphi, u2ehi3]
      · linarith only [h929, h930, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h927, h929, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1194 | h1194
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1195 | h1195
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1196 | h1196
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1197 | h1197
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1198 | h1198
            · linarith only [h1198, h927, h928, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1200 | h1200
              · linarith only [h1197, h1200, h927, h928, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1202 | h1202
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1203 | h1203
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                        · linarith only [h1198, h1206, h927, h928, hlam]
                        · linarith only [h1203, h1205, h1206, h927, h928, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h1197, h1198, h1205, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1196, h1204, hlam]
                  · linarith only [h0, h1202, h1203, h927, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1196, h1202, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1213 | h1213
            · linarith only [h1213, h927, h928, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1215 | h1215
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1216 | h1216
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1217 | h1217
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1218 | h1218
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1219 | h1219
                      · linarith only [h1197, h1218, h1219, h927, h928, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1221 | h1221
                        · linarith only [h1213, h1221, h927, h928, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1216, h1221, h927, h928, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1196, h1218, hlam]
                  · linarith only [h0, h1196, h1217, hc24, hlam, hphi, u2ehi4]
                · linarith only [h0, h1195, h1216, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1229 | h1229
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1230 | h1230
                      · linarith only [h1197, h1230, h927, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1232 | h1232
                        · linarith only [h1213, h1232, h927, hlam]
                        · linarith only [h1227, h1232, h927, h928, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1196, h1227, h1229, h927, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h1227, h1228, h927, hc24, hlam, hphi, u2ehi2]
                · linarith only [h0, h1196, h1227, hc23, hlam, hphi, u2ehi4]
        · linarith only [h1194, h1196, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1194, h1195, hc24, hlam, hphi, u2ehi2]
    · linarith only [h0, h1194, h927, hlam]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h1242 | h1242
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1243 | h1243
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1244 | h1244
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1245 | h1245
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1246 | h1246
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1247 | h1247
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1248 | h1248
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1249 | h1249
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1250 | h1250
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1251 | h1251
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1252 | h1252
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1253 | h1253
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1254 | h1254
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1256 | h1256
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1257 | h1257
                                · rcases h1bigk with h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c | h1258c
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h0, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h927, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1248, h1249, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi3]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1248, h1250, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1241, h1250, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h927, hc01, hc12, hlam, hphi, p1258_1]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    rcases p1258_3 (m.d 0 1) (by simp) with h1267 | h1267
                                    · linarith only [h0, h1267, hlam]
                                    · linarith only [h1241, h1250, h1267, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    rcases p1258_3 (m.d 0 1) (by simp) with h1270 | h1270
                                    · linarith only [h0, h1270, hlam]
                                    · linarith only [h1241, h1270, hlam]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1241, h1250, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1248, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    rcases p1258_3 (m.d 0 1) (by simp) with h1276 | h1276
                                    · linarith only [h1276, h927, hlam]
                                    · linarith only [h1241, h1248, h1250, h1276, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    rcases p1258_3 (m.d 0 1) (by simp) with h1279 | h1279
                                    · linarith only [h1279, h927, hlam]
                                    · linarith only [h1241, h1279, hlam]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1241, h1250, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1249, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1251, hlam, p1258_1]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    rcases p1258_3 (m.d 0 1) (by simp) with h1286 | h1286
                                    · linarith only [h0, h1250, h1286, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1258_1, u2ehi4]
                                    · linarith only [h1241, h1286, hlam]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1241, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1250, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1252, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [h1253, hlam, p1258_0]
                                  · have p1258_0 := h1258c.1
                                    have p1258_1 := h1258c.2.1
                                    have p1258_2 := h1258c.2.2.1
                                    have p1258_3 := h1258c.2.2.2
                                    linarith only [hlam, p1258_0]
                                · rcases h1bigk with h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h0, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h927, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1248, h1249, h1256, h1257, h927, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1294_1]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1248, h1250, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1294_1, u2ehi4]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1241, h1250, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1294_1, u2ehi4]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h927, hc01, hc12, hlam, hphi, p1294_1]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1249, h1256, h1257, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1294_1]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    rcases p1294_3 (m.d 0 1) (by simp) with h1304 | h1304
                                    · linarith only [h0, h1304, hlam]
                                    · linarith only [h1241, h1304, hlam]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1241, h1250, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1294_1, u2ehi4]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1248, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1248, h1249, h1256, h1257, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1294_1]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    rcases p1294_3 (m.d 0 1) (by simp) with h1311 | h1311
                                    · linarith only [h1311, h927, hlam]
                                    · linarith only [h1241, h1311, hlam]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1241, h1250, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1294_1, u2ehi4]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1249, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1251, hlam, p1294_1]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    rcases p1294_3 (m.d 0 1) (by simp) with h1318 | h1318
                                    · linarith only [h0, h1250, h1318, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1294_1, u2ehi4]
                                    · linarith only [h1241, h1318, hlam]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1241, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1250, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1252, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [h1253, hlam, p1294_0]
                                  · have p1294_0 := h1294c.1
                                    have p1294_1 := h1294c.2.1
                                    have p1294_2 := h1294c.2.2.1
                                    have p1294_3 := h1294c.2.2.2
                                    linarith only [hlam, p1294_0]
                              · linarith only [h1241, h1248, h1253, h1256, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1241, h1248, h1252, h1255, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1328 | h1328
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1329 | h1329
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1330 | h1330
                                · rcases h1bigk with h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c | h1331c
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h0, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h927, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1248, h1251, h1254, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi3]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1248, h1250, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1241, h1250, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h927, hc01, hc12, hlam, hphi, p1331_1]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1251, h1254, h1328, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    rcases p1331_3 (m.d 0 1) (by simp) with h1341 | h1341
                                    · linarith only [h0, h1341, hlam]
                                    · linarith only [h1241, h1341, hlam]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1241, h1250, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1248, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1248, h1251, h1254, h1328, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    rcases p1331_3 (m.d 0 1) (by simp) with h1348 | h1348
                                    · linarith only [h1348, h927, hlam]
                                    · linarith only [h1241, h1348, hlam]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1241, h1250, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1249, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1251, hlam, p1331_1]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    rcases p1331_3 (m.d 0 1) (by simp) with h1355 | h1355
                                    · linarith only [h1248, h1250, h1355, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1331_1, u2ehi4]
                                    · linarith only [h1241, h1355, hlam]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1241, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1250, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1252, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [h1253, hlam, p1331_0]
                                  · have p1331_0 := h1331c.1
                                    have p1331_1 := h1331c.2.1
                                    have p1331_2 := h1331c.2.2.1
                                    have p1331_3 := h1331c.2.2.2
                                    linarith only [hlam, p1331_0]
                                · linarith only [h1254, h1328, h1330, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                              · linarith only [h1241, h1248, h1253, h1254, h1328, h1329, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · linarith only [h1241, h1248, h1252, h1328, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1366 | h1366
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1367 | h1367
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1368 | h1368
                              · linarith only [h1249, h1253, h1368, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1370 | h1370
                                · linarith only [h1249, h1253, h1366, h1370, hc23, hlam, hphi, u2ehi3]
                                · rcases h1bigk with h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c | h1372c
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h0, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h927, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1248, h1249, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1372_1, u2ehi3]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1248, h1250, h1368, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1372_1, u2ehi3]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1241, h1247, h1249, h1253, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1372_1, u2ehi3]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h927, hc01, hc12, hlam, hphi, p1372_1]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    rcases p1372_3 (m.d 0 1) (by simp) with h1381 | h1381
                                    · linarith only [h0, h1381, hlam]
                                    · linarith only [h1241, h1247, h1253, h1381, hlam]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    rcases p1372_3 (m.d 0 1) (by simp) with h1384 | h1384
                                    · linarith only [h0, h1384, hlam]
                                    · linarith only [h1241, h1384, hlam]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1241, h1247, h1249, h1253, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1372_1, u2ehi3]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1248, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    rcases p1372_3 (m.d 0 1) (by simp) with h1390 | h1390
                                    · linarith only [h1390, h927, hlam]
                                    · linarith only [h1241, h1247, h1253, h1390, hlam]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    rcases p1372_3 (m.d 0 1) (by simp) with h1393 | h1393
                                    · linarith only [h1393, h927, hlam]
                                    · linarith only [h1241, h1393, hlam]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1241, h1247, h1253, hlam, p1372_1]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1249, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1251, hlam, p1372_1]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1253, hlam, p1372_1]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1241, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1250, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1252, hlam, p1372_0]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [h1241, h1249, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1372_1, u2ehi3]
                                  · have p1372_0 := h1372c.1
                                    have p1372_1 := h1372c.2.1
                                    have p1372_2 := h1372c.2.2.1
                                    have p1372_3 := h1372c.2.2.2
                                    linarith only [hlam, p1372_0]
                            · linarith only [h1241, h1248, h1252, h1367, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1242, h1245, h1247, h1251, h1253, h1366, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1241, h1244, h1252, h927, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h1245, h1251, h927, hlam]
                  · linarith only [h0, h1242, h1250, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1241, h1244, h1248, h1249, h927, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1241, h1242, h1244, h1248, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1413 | h1413
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1414 | h1414
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1415 | h1415
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1416 | h1416
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1417 | h1417
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1418 | h1418
                        · linarith only [h0, h1241, h1243, h1247, h1418, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1420 | h1420
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1422 | h1422
                              · linarith only [h1243, h1247, h1422, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1424 | h1424
                                · linarith only [h1243, h1247, h1420, h1424, hlam]
                                · rcases h1bigk with h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c | h1426c
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h0, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h927, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1413, h1414, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1426_1, u2ehi3]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1413, h1415, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1426_1, u2ehi4]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1241, h1415, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1426_1, u2ehi4]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h927, hc01, hc12, hlam, hphi, p1426_1]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    rcases p1426_3 (m.d 0 1) (by simp) with h1435 | h1435
                                    · linarith only [h0, h1435, hlam]
                                    · linarith only [h1241, h1418, h1435, hlam]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    rcases p1426_3 (m.d 0 1) (by simp) with h1438 | h1438
                                    · linarith only [h0, h1438, hlam]
                                    · linarith only [h1241, h1438, hlam]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1241, h1414, h1418, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1426_1, u2ehi3]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1413, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    rcases p1426_3 (m.d 0 1) (by simp) with h1444 | h1444
                                    · linarith only [h1444, h927, hlam]
                                    · linarith only [h1241, h1418, h1444, hlam]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    rcases p1426_3 (m.d 0 1) (by simp) with h1447 | h1447
                                    · linarith only [h1447, h927, hlam]
                                    · linarith only [h1241, h1447, hlam]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1241, h1418, hlam, p1426_1]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1414, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1416, hlam, p1426_1]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1418, hlam, p1426_1]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1241, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1415, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1417, hlam, p1426_0]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [h1241, h1414, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1426_1, u2ehi3]
                                  · have p1426_0 := h1426c.1
                                    have p1426_1 := h1426c.2.1
                                    have p1426_2 := h1426c.2.2.1
                                    have p1426_3 := h1426c.2.2.2
                                    linarith only [hlam, p1426_0]
                            · linarith only [h1241, h1413, h1417, h1421, h927, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h1245, h1247, h1420, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1241, h1244, h1417, h927, hc35, hlam, hphi, ht23, u2ehi4]
                    · linarith only [h1241, h1242, h1245, h1415, h1416, h927, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                  · linarith only [h0, h1241, h1243, h1247, h1415, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h1241, h1243, h1247, h1414, hlam]
              · linarith only [h0, h1241, h1243, h1247, h1413, hc23, hlam, hphi, u2ehi3]
          · linarith only [h1241, h1246, h927, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1468 | h1468
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1469 | h1469
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1470 | h1470
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1471 | h1471
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                  · linarith only [h1241, h1245, h1472, h927, hc34, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h0, h1243, h1472, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h1241, h1244, h1471, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1241, h1244, h1470, hc23, hlam, hphi, u2ehi4]
            · linarith only [h1241, h1245, h1469, h927, hlam]
          · linarith only [h1241, h1468, h927, hlam]
      · linarith only [h1242, h1244, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1242, h1243, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1481 | h1481
    · linarith only [h1242, h1481, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1483 | h1483
      · linarith only [h1242, h1483, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h1241, h1483, hlam]

end R2N4
