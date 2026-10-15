import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5254000 in
set_option maxHeartbeats 5254000 in
theorem r1l7_21_15_M_LI_L_I_s1_x0_x0_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h947 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.2.2.2
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 3 4 (by decide) (by decide) with h948 | h948
  · rcases m.htr 0 3 5 (by decide) (by decide) with h949 | h949
    · rcases m.htr 0 4 5 (by decide) (by decide) with h950 | h950
      · rcases m.htr 1 2 3 (by decide) (by decide) with h951 | h951
        · linarith only [h4, h947, h951, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h953 | h953
          · rcases m.htr 1 2 5 (by decide) (by decide) with h954 | h954
            · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
              · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
                · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h960 | h960
                        · linarith only [h0, h953, h960, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                        · linarith only [h1, h951, h953, h957, h958, h960, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h0, h1, h4, h949, h953, h957, h959, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h4, h948, h953, h958, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h965 | h965
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h966 | h966
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h967 | h967
                        · linarith only [h953, h957, h967, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h969 | h969
                          · linarith only [h953, h957, h965, h969, hlam]
                          · rcases h1bigk with h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c | h971c
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h954, h965, h967, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h951, h954, h965, h967, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              rcases p971_3 (m.d 0 1) (by simp) with h975 | h975
                              · rcases p971_3 (m.d 1 2) (by simp) with h976 | h976
                                · linarith only [h0, h976, hlam]
                                · linarith only [h953, h976, hlam]
                              · linarith only [h975, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              rcases p971_3 (m.d 0 1) (by simp) with h980 | h980
                              · rcases p971_3 (m.d 1 2) (by simp) with h981 | h981
                                · linarith only [h0, h981, hlam]
                                · linarith only [h954, h981, hlam]
                              · linarith only [h980, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h0, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h951, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h0, h953, h965, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h1, h951, hc15, hlam, hphi, ht01, ht0b, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h1, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h1, h953, h965, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h1, h954, h965, h967, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h2, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h953, hlam, p971_1]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h955, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h957, hlam, p971_1]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h3, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h954, hlam, p971_1]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h956, hlam, p971_0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [h3, h953, h965, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p971_1, u1elo0]
                            · have p971_0 := h971c.1
                              have p971_1 := h971c.2.1
                              have p971_2 := h971c.2.2.1
                              have p971_3 := h971c.2.2.2
                              linarith only [hlam, p971_0]
                      · linarith only [h4, h949, h966, hlam]
                    · linarith only [h4, h948, h965, hlam]
                · linarith only [h1, h949, h951, h954, h956, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h948, h951, h953, h955, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h4, h947, h953, h954, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1010 | h1010
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1012 | h1012
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1013 | h1013
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1014 | h1014
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1015 | h1015
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1016 | h1016
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1017 | h1017
                          · linarith only [h1, h1011, h1017, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                          · linarith only [h1013, h1017, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                        · linarith only [h1, h1011, h1013, h1016, h953, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                      · linarith only [h1015, h4, h949, hlam]
                    · linarith only [h1014, h4, h948, hlam]
                  · linarith only [h1, h1010, h1013, h948, h950, h953, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h1, h1011, h1012, h949, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · linarith only [h1, h1010, h1011, h948, h951, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1010, h4, h947, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1027 | h1027
        · linarith only [h1027, h4, h947, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1029 | h1029
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1030 | h1030
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1031 | h1031
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1032 | h1032
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1033 | h1033
                  · linarith only [h1033, h2, h950, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1035 | h1035
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1037 | h1037
                        · linarith only [h1029, h1037, h950, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1039 | h1039
                          · linarith only [h1029, h1035, h1039, h2, h950, hlam]
                          · rcases h1bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1030, h1035, h1037, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1027, h1030, h1035, h1037, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              rcases p1041_3 (m.d 0 1) (by simp) with h1045 | h1045
                              · rcases p1041_3 (m.d 1 2) (by simp) with h1046 | h1046
                                · linarith only [h0, h1046, hlam]
                                · linarith only [h1029, h1046, hlam]
                              · linarith only [h1045, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              rcases p1041_3 (m.d 0 1) (by simp) with h1050 | h1050
                              · rcases p1041_3 (m.d 1 2) (by simp) with h1051 | h1051
                                · linarith only [h0, h1051, hlam]
                                · linarith only [h1030, h1051, hlam]
                              · linarith only [h1050, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h0, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1027, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h0, h1029, h1035, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1, h1027, hc15, hlam, hphi, ht01, ht0b, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1, h1029, h1035, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1, h1030, h1035, h1037, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h2, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1029, hlam, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1031, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1033, hlam, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h3, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1030, hlam, p1041_1]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1032, hlam, p1041_0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [h1029, h1035, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1041_1, u1elo0]
                            · have p1041_0 := h1041c.1
                              have p1041_1 := h1041c.2.1
                              have p1041_2 := h1041c.2.2.1
                              have p1041_3 := h1041c.2.2.2
                              linarith only [hlam, p1041_0]
                      · linarith only [h1036, h4, h949, hlam]
                    · linarith only [h1035, h4, h948, hlam]
                · linarith only [h1, h1027, h1030, h1032, h949, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h1027, h1029, h1031, h948, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · linarith only [h1029, h1030, h4, h947, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1080 | h1080
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1082 | h1082
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1083 | h1083
                  · linarith only [h1083, h2, h950, hlam]
                  · linarith only [h1029, h1080, h1083, hlam]
                · linarith only [h1, h1029, h1080, h1081, h1082, h949, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
              · linarith only [h1, h1027, h1080, h1081, h948, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1080, h4, h947, hc12, hc23, hlam, hphi]
    · linarith only [h4, h947, h949, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1090 | h1090
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1091 | h1091
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1092 | h1092
        · linarith only [h1092, h4, h947, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1094 | h1094
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1095 | h1095
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1096 | h1096
              · linarith only [h1, h1096, h948, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h1092, h1094, h1096, hlam]
            · linarith only [h1094, h1095, h4, h947, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1100 | h1100
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1101 | h1101
              · linarith only [h1090, h1101, h948, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1103 | h1103
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1105 | h1105
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1106 | h1106
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1107 | h1107
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1108 | h1108
                          · rcases h1bigk with h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c | h1109c
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1100, h1106, h1108, hc45, hlam, hphi, ht01, ht0b, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1092, h1100, h1106, h1108, hc45, hlam, hphi, ht01, ht0b, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1092, h1100, h1101, h1106, h1108, hc45, hlam, hphi, ht01, ht0b, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              rcases p1109_3 (m.d 0 1) (by simp) with h1114 | h1114
                              · rcases p1109_3 (m.d 1 2) (by simp) with h1115 | h1115
                                · linarith only [h0, h1115, hlam]
                                · linarith only [h1100, h1115, hlam]
                              · linarith only [h1114, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h0, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1092, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1094, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h0, h1100, h1105, h1106, h1108, h4, h948, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1109_1]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1101, hlam, p1109_1]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1, h1100, h1105, h1106, h1108, h948, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1109_1]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h2, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1100, h1106, h1108, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1100, h1106, h1108, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1109_1, u1elo0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h3, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1100, hlam, p1109_1]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1103, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [h1104, hlam, p1109_0]
                            · have p1109_0 := h1109c.1
                              have p1109_1 := h1109c.2.1
                              have p1109_2 := h1109c.2.2.1
                              have p1109_3 := h1109c.2.2.2
                              linarith only [hlam, p1109_0]
                          · linarith only [h0, h1091, h1100, h1108, h4, h948, hc04, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h1100, h1104, h1105, h1106, h1107, h4, h948, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo4]
                      · linarith only [h1090, h1106, h948, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1142 | h1142
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1143 | h1143
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1144 | h1144
                          · rcases h1bigk with h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c | h1145c
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1100, h1142, h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1092, h1100, h1142, h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1094, h1100, h1142, h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              rcases p1145_3 (m.d 0 1) (by simp) with h1150 | h1150
                              · rcases p1145_3 (m.d 1 2) (by simp) with h1151 | h1151
                                · linarith only [h0, h1151, hlam]
                                · linarith only [h1100, h1151, hlam]
                              · linarith only [h1150, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h0, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1092, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1094, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h0, h1105, h4, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1100, h1101, hc25, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo3]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1101, hlam, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1, h1100, h1142, h1144, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h2, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1100, h1142, h1144, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h0, h1100, h1105, h1142, h1144, h2, h4, hc13, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1100, h1142, h1144, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p1145_1, u1elo0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h3, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1100, hlam, p1145_1]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1103, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [h1104, hlam, p1145_0]
                            · have p1145_0 := h1145c.1
                              have p1145_1 := h1145c.2.1
                              have p1145_2 := h1145c.2.2.1
                              have p1145_3 := h1145c.2.2.2
                              linarith only [hlam, p1145_0]
                          · linarith only [h0, h1100, h1105, h1142, h1144, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h1091, h1094, h1100, h1142, h1143, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1090, h1142, h4, hlam]
                  · linarith only [h1091, h1101, h1103, h1104, h2, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h1, h1090, h1092, h1100, h1103, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
            · linarith only [h1100, h4, h947, hc12, hc23, hlam, hphi]
      · linarith only [h1091, h4, h947, h948, hlam]
    · linarith only [h1090, h4, h947, hlam]

end R2N4
