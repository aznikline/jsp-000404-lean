import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h947 | h947
  · rcases m.htr 0 2 5 (by decide) (by decide) with h948 | h948
    · linarith only [h4, h948, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h950 | h950
      · rcases m.htr 0 4 5 (by decide) (by decide) with h951 | h951
        · linarith only [h4, h947, h951, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h953 | h953
          · linarith only [h4, h953, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h955 | h955
            · rcases m.htr 1 2 5 (by decide) (by decide) with h956 | h956
              · linarith only [h0, h948, h956, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h958 | h958
                · rcases m.htr 1 3 5 (by decide) (by decide) with h959 | h959
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h960 | h960
                    · linarith only [h2, h951, h960, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h962 | h962
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h963 | h963
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h964 | h964
                          · linarith only [h0, h2, h948, h951, h955, h963, h964, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h966 | h966
                            · linarith only [h948, h962, h964, h966, hc02, hlam, hphi, u2elo3]
                            · rcases h1bigk with h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c | h968c
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                rcases p968_3 (m.d 0 1) (by simp) with h970 | h970
                                · rcases p968_3 (m.d 1 2) (by simp) with h971 | h971
                                  · linarith only [h971, hlam, p968_0]
                                  · rcases p968_3 (m.d 1 3) (by simp) with h973 | h973
                                    · linarith only [h1, h973, hlam]
                                    · linarith only [h953, h973, hlam]
                                · linarith only [h970, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h959, hc01, hlam, hphi, ht0b, ht5b, p968_1, u5ehi3]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                rcases p968_3 (m.d 0 1) (by simp) with h978 | h978
                                · rcases p968_3 (m.d 1 2) (by simp) with h979 | h979
                                  · linarith only [h0, h979, hlam]
                                  · linarith only [h955, h979, hlam]
                                · linarith only [h978, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                rcases p968_3 (m.d 0 1) (by simp) with h983 | h983
                                · rcases p968_3 (m.d 1 2) (by simp) with h984 | h984
                                  · linarith only [h0, h984, hlam]
                                  · rcases p968_3 (m.d 1 3) (by simp) with h986 | h986
                                    · linarith only [h1, h986, hlam]
                                    · linarith only [h959, h986, hlam]
                                · linarith only [h983, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h0, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h953, hlam, p968_1]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h0, h948, h955, h962, h963, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p968_1, u2elo2]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h956, hlam, p968_1]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h1, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h1, h4, hc12, hlam, hphi, p968_1, u2elo2]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                rcases p968_3 (m.d 0 1) (by simp) with h998 | h998
                                · rcases p968_3 (m.d 1 2) (by simp) with h999 | h999
                                  · linarith only [h953, h999, hlam]
                                  · linarith only [h955, h999, hlam]
                                · linarith only [h2, h998, hlam]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h1, h4, h955, h956, h962, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p968_1, u2elo2]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h2, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h955, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h958, hlam, p968_1]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h960, hlam, p968_1]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h3, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h3, h955, h962, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p968_1]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [h959, hlam, p968_0]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                rcases p968_3 (m.d 0 1) (by simp) with h1012 | h1012
                                · rcases p968_3 (m.d 1 2) (by simp) with h1013 | h1013
                                  · linarith only [h1013, h956, hlam]
                                  · linarith only [h1013, h955, hlam]
                                · linarith only [h1012, h2, hlam]
                              · have p968_0 := h968c.1
                                have p968_1 := h968c.2.1
                                have p968_2 := h968c.2.2.1
                                have p968_3 := h968c.2.2.2
                                linarith only [hlam, p968_0]
                        · linarith only [h4, h950, h963, hlam]
                      · linarith only [h1, h4, h958, h962, hlam]
                  · linarith only [h4, h950, h953, h955, h959, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · linarith only [h953, h955, h958, hlam]
            · linarith only [h947, h948, h955, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1023 | h1023
        · linarith only [h1023, h947, h948, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1025 | h1025
          · linarith only [h0, h1025, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1027 | h1027
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1028 | h1028
              · linarith only [h0, h1028, h948, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1030 | h1030
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1031 | h1031
                  · linarith only [h1, h1031, h950, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1033 | h1033
                    · linarith only [h1023, h1033, h2, h947, h948, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1035 | h1035
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1036 | h1036
                        · linarith only [h1036, h4, h950, hc02, hlam, hphi, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1038 | h1038
                          · linarith only [h0, h1023, h1027, h1038, h2, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                            · linarith only [h1035, h1036, h1038, h1040, h4, h947, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h0, h1027, h1035, h1036, h1040, h4, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1, h1027, h1030, h1035, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1025, h1027, h1030, hlam]
            · linarith only [h1027, h947, hc12, hlam, hphi, u2elo0]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1046 | h1046
    · linarith only [h1046, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1048 | h1048
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1049 | h1049
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1050 | h1050
          · linarith only [h1050, h4, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1052 | h1052
            · linarith only [h0, h1049, h1052, h947, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1054 | h1054
              · linarith only [h0, h1046, h1054, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1058 | h1058
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1059 | h1059
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1060 | h1060
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1061 | h1061
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1062 | h1062
                            · linarith only [h1, h1056, h1062, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                            · rcases h1bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                rcases p1064_3 (m.d 0 1) (by simp) with h1066 | h1066
                                · rcases p1064_3 (m.d 1 2) (by simp) with h1067 | h1067
                                  · linarith only [h1067, hlam, p1064_0]
                                  · rcases p1064_3 (m.d 1 3) (by simp) with h1069 | h1069
                                    · linarith only [h1, h1069, hlam]
                                    · linarith only [h1050, h1069, hlam]
                                · linarith only [h1066, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1057, hc01, hlam, hphi, ht0b, ht5b, p1064_1, u5ehi3]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1058, h1062, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                rcases p1064_3 (m.d 0 1) (by simp) with h1075 | h1075
                                · rcases p1064_3 (m.d 1 2) (by simp) with h1076 | h1076
                                  · linarith only [h0, h1076, hlam]
                                  · rcases p1064_3 (m.d 1 3) (by simp) with h1078 | h1078
                                    · linarith only [h1, h1078, hlam]
                                    · linarith only [h1057, h1078, hlam]
                                · linarith only [h1075, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h0, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1050, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1052, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1054, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1, h4, hc12, hlam, hphi, p1064_1, u2elo2]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1, h1058, h1062, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1064_1, u2elo2]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1, u2elo2, u5ehi1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h2, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1059, h2, h947, hc12, hlam, hphi, p1064_1, u2elo2]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1056, hlam, p1064_1]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1057, h1059, h2, h947, hlam, hphi, ht01, ht0b, ht12, ht5b, p1064_1, u2elo2, u5ehi3]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h3, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1049, h1059, h3, h947, hc12, hlam, hphi, p1064_1, u2elo2]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1057, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [h1058, hlam, p1064_0]
                              · have p1064_0 := h1064c.1
                                have p1064_1 := h1064c.2.1
                                have p1064_2 := h1064c.2.2.1
                                have p1064_3 := h1064c.2.2.2
                                linarith only [hlam, p1064_0]
                          · linarith only [h1049, h1061, h947, hlam]
                        · linarith only [h1048, h1060, h4, hlam]
                      · linarith only [h1, h1056, h1059, h4, hlam]
                    · linarith only [h1049, h1052, h1058, h947, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1048, h1050, h1057, h4, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1107 | h1107
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1108 | h1108
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1109 | h1109
                      · linarith only [h1056, h1107, h1109, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1111 | h1111
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1112 | h1112
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1113 | h1113
                            · rcases h1bigk with h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c | h1114c
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                rcases p1114_3 (m.d 0 1) (by simp) with h1116 | h1116
                                · rcases p1114_3 (m.d 1 2) (by simp) with h1117 | h1117
                                  · linarith only [h1117, hlam, p1114_0]
                                  · rcases p1114_3 (m.d 1 3) (by simp) with h1119 | h1119
                                    · linarith only [h1, h1119, hlam]
                                    · linarith only [h1050, h1119, hlam]
                                · linarith only [h1116, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1107, h1113, hc01, hlam, hphi, ht0b, ht5b, p1114_1, u5ehi4]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1056, h1107, h1113, hc01, hlam, hphi, ht0b, ht5b, p1114_1, u5ehi4]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                rcases p1114_3 (m.d 0 1) (by simp) with h1125 | h1125
                                · rcases p1114_3 (m.d 1 2) (by simp) with h1126 | h1126
                                  · linarith only [h0, h1126, hlam]
                                  · rcases p1114_3 (m.d 1 3) (by simp) with h1128 | h1128
                                    · linarith only [h1, h1128, hlam]
                                    · linarith only [h1107, h1128, hlam]
                                · linarith only [h1125, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h0, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1050, hlam, p1114_1]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1052, hlam, p1114_1]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1054, hlam, p1114_1]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1, h1109, h4, hc12, hc34, hlam, hphi, ht23, p1114_1]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1056, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1, h1107, h1109, h1113, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1114_1, u5ehi4]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h2, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h2, h947, hc12, hlam, hphi, p1114_1, u2elo3]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1050, h2, h947, hc12, hlam, hphi, p1114_1, u2elo3]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1107, h1113, h2, h947, hlam, hphi, ht01, ht0b, ht12, ht5b, p1114_1, u2elo3, u5ehi4]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h3, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1046, h1109, h1111, h3, hc12, hc34, hlam, hphi, ht23, p1114_1]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1107, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [h1108, hlam, p1114_0]
                              · have p1114_0 := h1114c.1
                                have p1114_1 := h1114c.2.1
                                have p1114_2 := h1114c.2.2.1
                                have p1114_3 := h1114c.2.2.2
                                linarith only [hlam, p1114_0]
                            · linarith only [h1046, h1109, h1111, h1113, hc02, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1108, h1112, h2, h947, hlam]
                        · linarith only [h1, h1107, h1111, h4, hlam]
                    · linarith only [h1049, h1052, h1108, h947, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1048, h1050, h1107, h4, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
          · linarith only [h0, h1048, h1157, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1159 | h1159
            · linarith only [h0, h1159, h947, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1161 | h1161
              · linarith only [h0, h1161, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1164 | h1164
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1165 | h1165
                    · linarith only [h1049, h1165, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1167 | h1167
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1168 | h1168
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1169 | h1169
                          · linarith only [h1049, h1167, h1169, h947, hc02, hlam, hphi, u2elo2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1171 | h1171
                            · linarith only [h1049, h1163, h1171, h2, hlam]
                            · rcases h1bigk with h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c | h1173c
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                rcases p1173_3 (m.d 0 1) (by simp) with h1175 | h1175
                                · rcases p1173_3 (m.d 1 2) (by simp) with h1176 | h1176
                                  · linarith only [h1176, hlam, p1173_0]
                                  · rcases p1173_3 (m.d 1 3) (by simp) with h1178 | h1178
                                    · linarith only [h1, h1178, hlam]
                                    · linarith only [h1157, h1178, hlam]
                                · linarith only [h1175, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1164, hc01, hlam, hphi, ht0b, ht5b, p1173_1, u5ehi3]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                rcases p1173_3 (m.d 0 1) (by simp) with h1183 | h1183
                                · rcases p1173_3 (m.d 1 2) (by simp) with h1184 | h1184
                                  · linarith only [h0, h1184, hlam]
                                  · rcases p1173_3 (m.d 1 3) (by simp) with h1186 | h1186
                                    · linarith only [h1, h1186, hlam]
                                    · linarith only [h1163, h1186, hlam]
                                · linarith only [h1183, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                rcases p1173_3 (m.d 0 1) (by simp) with h1190 | h1190
                                · rcases p1173_3 (m.d 1 2) (by simp) with h1191 | h1191
                                  · linarith only [h0, h1191, hlam]
                                  · rcases p1173_3 (m.d 1 3) (by simp) with h1193 | h1193
                                    · linarith only [h1, h1193, hlam]
                                    · linarith only [h1164, h1193, hlam]
                                · linarith only [h1190, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h0, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1157, hlam, p1173_1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1159, hlam, p1173_1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1161, hlam, p1173_1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1, h4, hc12, hlam, hphi, p1173_1, u2elo2]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1, h1159, h4, hc12, hlam, hphi, p1173_1, u2elo2]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, p1173_1, u2elo2, u5ehi1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h2, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h2, h947, hc12, hlam, hphi, p1173_1, u2elo3]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1163, hlam, p1173_1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1165, hlam, p1173_1]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h3, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1048, h3, h4, hc12, hlam, hphi, p1173_1, u2elo2]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1164, hlam, p1173_0]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [h1048, h1159, h3, h4, hc12, hlam, hphi, p1173_1, u2elo2]
                              · have p1173_0 := h1173c.1
                                have p1173_1 := h1173c.2.1
                                have p1173_2 := h1173c.2.2.1
                                have p1173_3 := h1173c.2.2.2
                                linarith only [hlam, p1173_0]
                        · linarith only [h1048, h1168, h4, hlam]
                      · linarith only [h1, h1163, h1164, h1167, h2, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h1048, h1163, h1164, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1220 | h1220
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1221 | h1221
                    · linarith only [h1049, h1221, h2, hlam]
                    · linarith only [h1163, h1220, h1221, hlam]
                  · linarith only [h1048, h1157, h1220, h4, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1225 | h1225
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
          · linarith only [h0, h1226, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
            · linarith only [h0, h1225, h1228, h4, h947, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
              · linarith only [h0, h1230, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h1, h1048, h1233, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1235 | h1235
                    · linarith only [h1232, h1233, h1235, hlam]
                    · linarith only [h1225, h1228, h1235, h947, hc12, hlam, hphi, u2elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1238 | h1238
                  · linarith only [h0, h1048, h1232, h1238, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1240 | h1240
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1241 | h1241
                      · linarith only [h1226, h1232, h1241, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1243 | h1243
                        · linarith only [h1048, h1241, h1243, hc03, hc34, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1245 | h1245
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1246 | h1246
                            · rcases h1bigk with h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                rcases p1247_3 (m.d 0 1) (by simp) with h1249 | h1249
                                · rcases p1247_3 (m.d 1 2) (by simp) with h1250 | h1250
                                  · linarith only [h1250, hlam, p1247_0]
                                  · rcases p1247_3 (m.d 1 3) (by simp) with h1252 | h1252
                                    · linarith only [h1, h1252, hlam]
                                    · linarith only [h1226, h1252, hlam]
                                · linarith only [h1249, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                rcases p1247_3 (m.d 0 1) (by simp) with h1256 | h1256
                                · rcases p1247_3 (m.d 1 2) (by simp) with h1257 | h1257
                                  · linarith only [h0, h1257, hlam]
                                  · rcases p1247_3 (m.d 1 3) (by simp) with h1259 | h1259
                                    · linarith only [h1259, hlam, p1247_0]
                                    · rcases p1247_3 (m.d 1 4) (by simp) with h1261 | h1261
                                      · linarith only [h1261, h2, hlam]
                                      · linarith only [h1232, h1261, hlam]
                                · linarith only [h1256, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1240, hc01, hlam, hphi, ht0b, ht5b, p1247_1, u5ehi4]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                rcases p1247_3 (m.d 0 1) (by simp) with h1266 | h1266
                                · rcases p1247_3 (m.d 1 2) (by simp) with h1267 | h1267
                                  · linarith only [h0, h1267, hlam]
                                  · rcases p1247_3 (m.d 1 3) (by simp) with h1269 | h1269
                                    · linarith only [h1, h1269, hlam]
                                    · rcases p1247_3 (m.d 1 4) (by simp) with h1271 | h1271
                                      · linarith only [h1271, h2, hlam]
                                      · linarith only [h1240, h1271, hlam]
                                · linarith only [h1266, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h0, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1226, hlam, p1247_1]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1228, hlam, p1247_1]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1230, hlam, p1247_1]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1, h1243, h1245, h4, hc12, hlam, hphi, p1247_1, u2elo3]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1232, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1238, hlam, p1247_1]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h2, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h2, h947, hc12, hlam, hphi, p1247_1, u2elo3]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1226, h2, h947, hc12, hlam, hphi, p1247_1, u2elo3]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1240, h2, h947, hlam, hphi, ht01, ht0b, ht12, ht5b, p1247_1, u2elo3, u5ehi4]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h3, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1225, h3, h947, hc12, hlam, hphi, p1247_1, u2elo3]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1225, h1226, h3, h947, hc12, hlam, hphi, p1247_1, u2elo3]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [h1240, hlam, p1247_0]
                              · have p1247_0 := h1247c.1
                                have p1247_1 := h1247c.2.1
                                have p1247_2 := h1247c.2.2.1
                                have p1247_3 := h1247c.2.2.2
                                linarith only [hlam, p1247_0]
                            · linarith only [h1225, h1226, h1232, h1246, h947, hc12, hlam, hphi, u2elo3]
                          · linarith only [h1240, h1245, h2, h947, hlam]
                    · linarith only [h1225, h1228, h1240, h947, hc12, hlam, hphi, u2elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1298 | h1298
          · linarith only [h0, h1298, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1300 | h1300
            · linarith only [h0, h1300, h947, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1302 | h1302
              · linarith only [h0, h1046, h1302, h4, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1304 | h1304
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
                  · linarith only [h1, h1048, h1305, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1307 | h1307
                    · linarith only [h1225, h1307, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1309 | h1309
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1310 | h1310
                        · linarith only [h1, h1048, h1304, h1310, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1312 | h1312
                          · linarith only [h1225, h1312, h947, hc02, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1314 | h1314
                            · linarith only [h1, h1304, h1312, h1314, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h1bigk with h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c | h1316c
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                rcases p1316_3 (m.d 0 1) (by simp) with h1318 | h1318
                                · rcases p1316_3 (m.d 1 2) (by simp) with h1319 | h1319
                                  · linarith only [h1319, hlam, p1316_0]
                                  · rcases p1316_3 (m.d 1 3) (by simp) with h1321 | h1321
                                    · linarith only [h1, h1321, hlam]
                                    · linarith only [h1298, h1321, hlam]
                                · linarith only [h1318, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                rcases p1316_3 (m.d 0 1) (by simp) with h1325 | h1325
                                · rcases p1316_3 (m.d 1 2) (by simp) with h1326 | h1326
                                  · linarith only [h0, h1326, hlam]
                                  · rcases p1316_3 (m.d 1 3) (by simp) with h1328 | h1328
                                    · linarith only [h1328, hlam, p1316_0]
                                    · rcases p1316_3 (m.d 1 4) (by simp) with h1330 | h1330
                                      · linarith only [h1330, h2, hlam]
                                      · rcases p1316_3 (m.d 1 5) (by simp) with h1332 | h1332
                                        · linarith only [h1332, h3, hlam]
                                        · linarith only [h1305, h1332, hlam]
                                · linarith only [h1325, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                rcases p1316_3 (m.d 0 1) (by simp) with h1336 | h1336
                                · rcases p1316_3 (m.d 1 2) (by simp) with h1337 | h1337
                                  · linarith only [h0, h1337, hlam]
                                  · rcases p1316_3 (m.d 1 3) (by simp) with h1339 | h1339
                                    · linarith only [h1, h1339, hlam]
                                    · linarith only [h1304, h1339, hlam]
                                · linarith only [h1336, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                rcases p1316_3 (m.d 0 1) (by simp) with h1343 | h1343
                                · rcases p1316_3 (m.d 1 2) (by simp) with h1344 | h1344
                                  · linarith only [h0, h1344, hlam]
                                  · rcases p1316_3 (m.d 1 3) (by simp) with h1346 | h1346
                                    · linarith only [h1, h1346, hlam]
                                    · rcases p1316_3 (m.d 1 4) (by simp) with h1348 | h1348
                                      · linarith only [h1348, h2, hlam]
                                      · rcases p1316_3 (m.d 1 5) (by simp) with h1350 | h1350
                                        · linarith only [h1350, hlam, p1316_0]
                                        · rcases h1emin with h1352 | h1352 | h1352 | h1352 | h1352
                                          · rcases h5bigk with h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c | h1353c
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1046, hlam, hphi, ht01, ht0b, ht12, ht5b, p1353_1, u2elo4, u5ehi1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1046, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1048, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1225, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h3, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1302, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1305, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1307, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p1353_1, u2elo4, u5ehi0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p1353_1, u2elo4, u5ehi1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1310, hlam, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1312, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1, h1048, h1304, h1314, hc34, hc45, hlam, hphi, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1304, h1305, h1314, hc34, hc45, hlam, hphi, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h0, h1046, h1314, hc12, hc45, hlam, hphi, ht23, ht34, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1314, hlam, p1353_0]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1, h1048, h1304, hc34, hc45, hlam, hphi, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1304, h1305, hc34, hc45, hlam, hphi, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h0, h1310, h4, hc12, hc45, hlam, hphi, ht23, ht34, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [h1, h1048, h1304, hc34, hc45, hlam, hphi, p1353_1]
                                            · have p1353_0 := h1353c.1
                                              have p1353_1 := h1353c.2.1
                                              have p1353_2 := h1353c.2.2.1
                                              have p1353_3 := h1353c.2.2.2
                                              linarith only [hlam, p1353_0]
                                          · linarith only [h0, h1352, h4, hlam, ht12, u2elo2]
                                          · linarith only [h1305, h1352, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1316_1]
                                          · linarith only [h1352, h2, h947, hlam, ht12, u2elo3]
                                          · linarith only [h1352, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1316_1]
                                · linarith only [h1343, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h0, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1298, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1300, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1302, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1, h1048, hc12, hc35, hlam, hphi, ht23, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1, h1300, h1310, h4, hc12, hlam, hphi, p1316_1, u2elo4]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1305, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h2, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1225, h2, hc12, hc45, hlam, hphi, ht23, ht34, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1304, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1307, hlam, p1316_1]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h3, hlam, p1316_0]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1046, h3, hc12, hlam, hphi, p1316_1, u2elo4]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1046, h1298, h3, hc12, hlam, hphi, p1316_1, u2elo4]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [h1046, h1300, h3, hc12, hlam, hphi, p1316_1, u2elo4]
                              · have p1316_0 := h1316c.1
                                have p1316_1 := h1316c.2.1
                                have p1316_2 := h1316c.2.2.1
                                have p1316_3 := h1316c.2.2.2
                                linarith only [hlam, p1316_0]
                      · linarith only [h1, h1304, h1309, h4, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1405 | h1405
                  · linarith only [h1048, h1225, h1304, h1405, h2, hc03, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1407 | h1407
                    · linarith only [h1225, h1407, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1409 | h1409
                      · linarith only [h1298, h1304, h1409, hc12, hlam, hphi, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1411 | h1411
                        · linarith only [h0, h1048, h1409, h1411, h4, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1413 | h1413
                          · linarith only [h1225, h1298, h1304, h1413, h2, hc12, hlam, hphi, u2elo3]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1415 | h1415
                            · linarith only [h0, h1409, h1413, h1415, h4, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1409, h1415, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0_x0 m hb1 hb2 hb5 h0 h1 h2 h3 h4
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0_x1 m hb1 hb2 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1418 | h1418
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1419 | h1419
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1420 | h1420
      · linarith only [h0, h1420, h3, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1422 | h1422
        · linarith only [h1418, h1420, h1422, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1424 | h1424
          · linarith only [h1419, h1420, h1424, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1427 | h1427
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1428 | h1428
                · linarith only [h1420, h1428, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1426, h1428, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
              · linarith only [h1419, h1426, h1427, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
            · linarith only [h1418, h1420, h1426, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1433 | h1433
      · linarith only [h1419, h1433, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1435 | h1435
        · linarith only [h1418, h1419, h1435, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1437 | h1437
          · linarith only [h1437, h2, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1440 | h1440
              · linarith only [h0, h1419, h1440, h3, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1442 | h1442
                · linarith only [h0, h1419, h1433, h1442, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi0]
                · linarith only [h1439, h1440, h1442, h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · linarith only [h1418, h1419, h1439, hc12, hlam, hphi, u2elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1446 | h1446
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1447 | h1447
      · linarith only [h1418, h1447, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1449 | h1449
        · linarith only [h1, h1449, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1451 | h1451
          · linarith only [h1418, h1446, h1451, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1453 | h1453
            · linarith only [h1418, h1453, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
                · linarith only [h1, h1447, h1453, h1456, h3, hlam]
                · linarith only [h1, h1453, h1455, h1456, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1418, h1446, h1455, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1460 | h1460
      · linarith only [h1418, h1460, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1462 | h1462
        · linarith only [h1, h1462, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1464 | h1464
          · linarith only [h1464, h2, h3, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1466 | h1466
            · linarith only [h1418, h1466, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1468 | h1468
              · linarith only [h0, h1446, h1468, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                · linarith only [h0, h1418, h1460, h1470, h3, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1468, h1470, h2, h3, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x0 m hb1 hb2 hb5 h0 h1 h2 h3
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0_x1 m hb1 hb2 hb5 h0 h1 h2 h3

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1473 | h1473
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1474 | h1474
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1475 | h1475
      · linarith only [h0, h1475, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1477 | h1477
        · linarith only [h1475, h1477, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1479 | h1479
          · linarith only [h1474, h1475, h1479, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1481 | h1481
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1483 | h1483
                · linarith only [h0, h1475, h1483, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1482, h1483, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h1474, h1477, h1482, hc12, hlam, hphi, u2elo4]
            · linarith only [h1473, h1481, h2, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1488 | h1488
      · linarith only [h1473, h1474, h1488, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1490 | h1490
        · linarith only [h1474, h1490, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1492 | h1492
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1493 | h1493
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1494 | h1494
              · linarith only [h1474, h1494, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1496 | h1496
                · linarith only [h0, h1, h1488, h1492, h1496, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                · linarith only [h1, h1492, h1496, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
            · linarith only [h1, h1492, h1493, h2, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1500 | h1500
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
              · linarith only [h1474, h1501, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1503 | h1503
                · linarith only [h0, h1488, h1503, hlam]
                · linarith only [h1, h1501, h1503, h2, hc12, hlam, hphi, u2elo3]
            · linarith only [h1473, h1500, h2, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1507 | h1507
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1508 | h1508
      · linarith only [h0, h1508, h2, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1510 | h1510
        · linarith only [h1508, h1510, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1512 | h1512
          · linarith only [h1507, h1508, h1512, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1514 | h1514
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1515 | h1515
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1516 | h1516
                · linarith only [h1508, h1516, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1515, h1516, h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
              · linarith only [h1507, h1515, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1520 | h1520
              · linarith only [h0, h1514, h1520, h2, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1507, h1508, h1520, hc12, hlam, hphi, u2elo3]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1523 | h1523
      · linarith only [h0, h1507, h1523, h2, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1525 | h1525
        · linarith only [h1523, h1525, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1527 | h1527
          · linarith only [h1, h1473, h1527, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1529 | h1529
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1530 | h1530
              · linarith only [h0, h1507, h1530, h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1532 | h1532
                · linarith only [h0, h1473, h1507, h1523, h1529, h1532, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1, h1530, h1532, h2, hc12, hlam, hphi, u2elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1535 | h1535
              · linarith only [h1507, h1535, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1537 | h1537
                · linarith only [h0, h1529, h1537, h2, hc24, hc45, hlam, hphi]
                · linarith only [h1, h1535, h1537, h2, hc12, hlam, hphi, u2elo3]

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x0 m hb1 hb2 hb5 h0 h1 h2
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0_x1 m hb1 hb2 hb5 h0 h1 h2

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1540 | h1540
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1541 | h1541
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1542 | h1542
      · linarith only [h0, h1, h1542, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1544 | h1544
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1545 | h1545
          · linarith only [h1542, h1545, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1547 | h1547
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1548 | h1548
              · linarith only [h1542, h1544, h1548, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1550 | h1550
                · linarith only [h1542, h1550, hc02, hlam, hphi, u2elo1]
                · linarith only [h1, h1541, h1550, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
            · linarith only [h1, h1541, h1547, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1554 | h1554
          · linarith only [h1544, h1554, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1556 | h1556
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1557 | h1557
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1558 | h1558
                · linarith only [h0, h1, h1542, h1558, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h1, h1540, h1557, h1558, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1561 | h1561
                · linarith only [h0, h1542, h1561, hlam]
                · linarith only [h0, h1, h1561, hc12, hlam, hphi, u2elo2]
            · linarith only [h1, h1541, h1556, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1565 | h1565
      · linarith only [h0, h1, h1565, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1567 | h1567
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1568 | h1568
          · linarith only [h1565, h1568, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1570 | h1570
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1571 | h1571
              · linarith only [h1565, h1567, h1571, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1573 | h1573
                · linarith only [h0, h1, h1565, h1573, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1573, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1576 | h1576
              · linarith only [h1565, h1567, h1576, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1578 | h1578
                · linarith only [h0, h1, h1565, h1578, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1578, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1581 | h1581
          · linarith only [h1567, h1581, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1583 | h1583
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1584 | h1584
              · linarith only [h1540, h1541, h1584, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1586 | h1586
                · linarith only [h1565, h1586, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h1586, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1589 | h1589
              · linarith only [h1, h1540, h1583, h1589, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1591 | h1591
                · linarith only [h0, h1, h1583, h1591, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h1591, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1594 | h1594
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1595 | h1595
      · linarith only [h0, h1, h1595, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1597 | h1597
        · linarith only [h1540, h1594, h1595, h1597, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1599 | h1599
          · linarith only [h1595, h1599, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1601 | h1601
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1602 | h1602
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
                · linarith only [h0, h1, h1595, h1603, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1603, hc12, hlam, hphi, u2elo2]
              · linarith only [h1540, h1594, h1602, hlam]
            · linarith only [h1, h1594, h1601, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1608 | h1608
      · linarith only [h0, h1, h1608, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1610 | h1610
        · linarith only [h0, h1540, h1608, h1610, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1612 | h1612
          · linarith only [h1608, h1612, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1614 | h1614
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1615 | h1615
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1616 | h1616
                · linarith only [h1608, h1616, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1, h1616, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1619 | h1619
                · linarith only [h0, h1, h1608, h1619, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h0, h1, h1619, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1622 | h1622
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1623 | h1623
                · linarith only [h0, h1, h1614, h1623, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h1623, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1626 | h1626
                · linarith only [h0, h1, h1614, h1626, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1, h1626, hc12, hlam, hphi, u2elo2]

set_option maxHeartbeats 4278000 in
set_option maxHeartbeats 4278000 in
theorem r1l7_11_12_25_L_I_L_0_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h1emin := hb1.2.1
  have h2elo := hb2.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x0 m hb1 hb2 hb5 h0 h1
  · exact r1l7_11_12_25_L_I_L_0_M_IR_x0_x1 m hb1 hb2 hb5 h0 h1

end R2N4
