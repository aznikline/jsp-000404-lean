import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h987 | h987
  · rcases m.htr 0 1 5 (by decide) (by decide) with h988 | h988
    · linarith only [h1, h988, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h990 | h990
      · linarith only [h0, h1, h990, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h992 | h992
        · rcases m.htr 0 3 5 (by decide) (by decide) with h993 | h993
          · rcases m.htr 0 4 5 (by decide) (by decide) with h994 | h994
            · linarith only [h1, h987, h994, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h996 | h996
              · linarith only [h0, h1, h990, h996, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h998 | h998
                · linarith only [h0, h1, h998, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h1, h1000, h987, h998, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1004 | h1004
                        · linarith only [h1003, h1004, h987, h988, h994, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1006 | h1006
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1007 | h1007
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1008 | h1008
                              · linarith only [h1004, h1008, h987, h988, h998, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1010 | h1010
                                · linarith only [h1000, h1002, h1008, h1010, h987, h988, hlam]
                                · rcases h3bigk with h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c | h1012c
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1, hlam, p1012_1]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h990, hlam, p1012_1]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    rcases p1012_3 (m.d 0 3) (by simp) with h1016 | h1016
                                    · rcases p1012_3 (m.d 1 3) (by simp) with h1017 | h1017
                                      · rcases p1012_3 (m.d 2 3) (by simp) with h1018 | h1018
                                        · rcases p1012_3 (m.d 3 4) (by simp) with h1019 | h1019
                                          · linarith only [h1019, hlam, p1012_0]
                                          · rcases p1012_3 (m.d 3 5) (by simp) with h1021 | h1021
                                            · linarith only [h1021, h993, hlam]
                                            · linarith only [h1010, h1021, hlam]
                                        · linarith only [h1006, h1018, hlam]
                                      · linarith only [h1002, h1017, hlam]
                                    · linarith only [h1016, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, p1012_1, u1elo2, u5ehi3]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1, h987, h998, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1012_1, u1elo2]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h996, hlam, p1012_1]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    rcases p1012_3 (m.d 0 3) (by simp) with h1031 | h1031
                                    · linarith only [h1, h1031, hlam]
                                    · linarith only [h1031, h992, hlam]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p1012_1, u1elo2, u5ehi3]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h993, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1012_1, u5ehi3]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1, h987, h998, hc12, hc23, hlam, hphi, p1012_1]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    rcases p1012_3 (m.d 0 3) (by simp) with h1038 | h1038
                                    · linarith only [h1038, h990, hlam]
                                    · linarith only [h1038, h992, hlam]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    rcases p1012_3 (m.d 0 3) (by simp) with h1041 | h1041
                                    · linarith only [h1041, h990, hlam]
                                    · linarith only [h1041, h993, hlam]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h992, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1002, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1006, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1010, hlam, p1012_1]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h993, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1003, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1007, hlam, p1012_0]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [h1, h993, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1012_1, u1elo2]
                                  · have p1012_0 := h1012c.1
                                    have p1012_1 := h1012c.2.1
                                    have p1012_2 := h1012c.2.2.1
                                    have p1012_3 := h1012c.2.2.2
                                    linarith only [hlam, p1012_0]
                            · linarith only [h0, h1, h1007, h990, h993, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1003, h1006, h988, h996, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h1003, h993, hlam]
                    · linarith only [h1, h1002, h987, h998, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1058 | h1058
            · linarith only [h1, h1058, h987, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1060 | h1060
              · linarith only [h0, h1, h1060, h990, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1062 | h1062
                · linarith only [h0, h1, h1062, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1064 | h1064
                  · linarith only [h1, h1062, h1064, h987, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1066 | h1066
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1067 | h1067
                      · linarith only [h1, h1067, h993, hc01, hlam, hphi, u1elo2]
                      · linarith only [h1, h1062, h1067, h987, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h1062, h1066, h987, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h987, h992, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1072 | h1072
    · linarith only [h1, h1072, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1074 | h1074
      · linarith only [h0, h1, h1074, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1076 | h1076
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1077 | h1077
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1078 | h1078
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1079 | h1079
              · linarith only [h0, h1, h1074, h1079, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1081 | h1081
                · linarith only [h0, h1, h1081, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1083 | h1083
                  · linarith only [h0, h1, h1083, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1085 | h1085
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1086 | h1086
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1087 | h1087
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1088 | h1088
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1089 | h1089
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1090 | h1090
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1091 | h1091
                                · linarith only [h1, h1076, h1091, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                                · rcases h3bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1, hlam, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1074, hlam, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    rcases p1093_3 (m.d 0 3) (by simp) with h1097 | h1097
                                    · rcases p1093_3 (m.d 1 3) (by simp) with h1098 | h1098
                                      · rcases p1093_3 (m.d 2 3) (by simp) with h1099 | h1099
                                        · rcases p1093_3 (m.d 3 4) (by simp) with h1100 | h1100
                                          · linarith only [h1100, hlam, p1093_0]
                                          · rcases p1093_3 (m.d 3 5) (by simp) with h1102 | h1102
                                            · linarith only [h1077, h1102, hlam]
                                            · linarith only [h1091, h1102, hlam]
                                        · linarith only [h1088, h1099, hlam]
                                      · linarith only [h1085, h1098, hlam]
                                    · linarith only [h1097, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1, hlam, hphi, ht01, ht0b, ht5b, p1093_1, u1elo2, u5ehi3]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, p1093_1, u1elo2]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1079, hlam, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    rcases p1093_3 (m.d 0 3) (by simp) with h1112 | h1112
                                    · linarith only [h1, h1112, hlam]
                                    · linarith only [h1076, h1112, hlam]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, hphi, ht01, ht0b, ht5b, p1093_1, u1elo2, u5ehi3]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1076, h1078, h1091, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h0, h1072, h1085, h1087, hc12, hc23, hlam, hphi, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    rcases p1093_3 (m.d 0 3) (by simp) with h1119 | h1119
                                    · linarith only [h1074, h1119, hlam]
                                    · linarith only [h1076, h1119, hlam]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    rcases p1093_3 (m.d 0 3) (by simp) with h1122 | h1122
                                    · linarith only [h1074, h1122, hlam]
                                    · linarith only [h1077, h1122, hlam]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1076, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1085, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1088, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1091, hlam, p1093_1]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1077, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1086, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1089, hlam, p1093_0]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [h1, h1077, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1, u1elo2]
                                  · have p1093_0 := h1093c.1
                                    have p1093_1 := h1093c.2.1
                                    have p1093_2 := h1093c.2.2.1
                                    have p1093_3 := h1093c.2.2.2
                                    linarith only [hlam, p1093_0]
                              · linarith only [h0, h1072, h1078, h1081, h1087, h1090, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h0, h1, h1074, h1077, h1089, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · linarith only [h0, h1, h1079, h1088, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1076, h1078, h1087, h987, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h0, h1, h1086, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1076, h1085, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1141 | h1141
              · linarith only [h0, h1141, h987, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1143 | h1143
                · linarith only [h0, h1, h1143, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1145 | h1145
                  · linarith only [h0, h1, h1145, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1147 | h1147
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1148 | h1148
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1149 | h1149
                        · linarith only [h1078, h1147, h1149, h987, hc01, hlam, hphi, u1elo2]
                        · linarith only [h0, h1149, h987, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h0, h1, h1148, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h1, h1076, h1147, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1154 | h1154
            · linarith only [h1076, h1077, h1154, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1156 | h1156
              · linarith only [h0, h1, h1156, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
                · linarith only [h0, h1, h1158, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1160 | h1160
                  · linarith only [h0, h1, h1160, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1162 | h1162
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1163 | h1163
                      · linarith only [h1076, h1077, h1163, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · linarith only [h0, h1, h1163, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h1162, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1167 | h1167
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1169 | h1169
              · linarith only [h0, h1, h1169, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
                · linarith only [h0, h1, h1171, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1173 | h1173
                  · linarith only [h0, h1, h1173, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1175 | h1175
                    · linarith only [h1076, h1167, h1175, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi3]
                    · linarith only [h0, h1, h1175, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1076, h1167, h1168, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1179 | h1179
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1180 | h1180
              · linarith only [h0, h1, h1180, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1182 | h1182
                · linarith only [h0, h1, h1182, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1184 | h1184
                  · linarith only [h0, h1, h1184, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1186 | h1186
                    · linarith only [h1, h1076, h1186, hc01, hlam, hphi, u1elo2]
                    · linarith only [h0, h1, h1186, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1189 | h1189
              · linarith only [h0, h1, h1189, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1191 | h1191
                · linarith only [h0, h1, h1191, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
                  · linarith only [h0, h1, h1193, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                    · linarith only [h1, h1076, h1195, hc01, hlam, hphi, u1elo2]
                    · linarith only [h0, h1, h1195, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_0_L_I_M_IR_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 5002000 in
set_option maxHeartbeats 5002000 in
theorem r1l7_11_13_25_L_0_L_I_M_IR_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1198 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1199 | h1199
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1200 | h1200
    · linarith only [h0, h1200, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1202 | h1202
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1203 | h1203
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1204 | h1204
          · linarith only [h0, h1198, h1204, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1206 | h1206
            · linarith only [h0, h1198, h1203, h1206, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1208 | h1208
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1209 | h1209
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1210 | h1210
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1211 | h1211
                    · linarith only [h1198, h1200, h1210, h1211, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · linarith only [h1198, h1200, h1203, h1210, h1211, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1214 | h1214
                    · linarith only [h0, h1198, h1210, h1214, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1198, h1203, h1210, h1214, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h1199, h1209, hlam]
              · linarith only [h0, h1199, h1202, h1208, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1219 | h1219
          · linarith only [h0, h1199, h1203, h1219, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1221 | h1221
            · linarith only [h0, h1199, h1221, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1223 | h1223
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1224 | h1224
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1225 | h1225
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1226 | h1226
                    · linarith only [h1198, h1200, h1203, h1225, h1226, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1228 | h1228
                      · linarith only [h1198, h1200, h1219, h1225, h1228, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1230 | h1230
                        · linarith only [h1199, h1200, h1203, h1221, h1225, h1230, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1232 | h1232
                          · linarith only [h1198, h1203, h1223, h1232, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1234 | h1234
                            · linarith only [h1200, h1223, h1228, h1234, hc01, hlam, hphi, u1elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1236 | h1236
                              · linarith only [h1199, h1200, h1224, h1230, h1236, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1238 | h1238
                                · linarith only [h1199, h1200, h1223, h1226, h1230, h1238, hc23, hc34, hlam, hphi]
                                · rcases h3bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1203, h1223, h1238, hc23, hc45, hlam, hphi, ht34, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1203, h1238, hc23, hc45, hlam, hphi, ht34, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1203, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1219, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1198, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1199, h1200, h1226, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1240_1, u1elo4]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1226, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1228, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1202, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1223, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1232, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1234, hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1238, hc03, hc45, hlam, hphi, ht34, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1223, h1238, hc23, hc45, hlam, hphi, ht34, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1238, hc23, hc45, hlam, hphi, ht34, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [hlam, p1240_0]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1238, hlam, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    rcases p1240_3 (m.d 0 3) (by simp) with h1261 | h1261
                                    · linarith only [h1261, hlam, p1240_0]
                                    · rcases p1240_3 (m.d 1 3) (by simp) with h1263 | h1263
                                      · linarith only [h1228, h1263, hlam]
                                      · rcases p1240_3 (m.d 2 3) (by simp) with h1265 | h1265
                                        · linarith only [h1234, h1265, hlam]
                                        · rcases p1240_3 (m.d 3 4) (by simp) with h1267 | h1267
                                          · linarith only [h1238, h1267, hlam]
                                          · linarith only [h1203, h1267, hlam]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    rcases p1240_3 (m.d 0 3) (by simp) with h1270 | h1270
                                    · linarith only [h1219, h1270, hlam]
                                    · linarith only [h1198, h1270, hlam]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    rcases p1240_3 (m.d 0 3) (by simp) with h1273 | h1273
                                    · linarith only [h1219, h1273, hlam]
                                    · linarith only [h1202, h1273, hlam]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [h1198, h1203, h1223, hc23, hc35, hlam, hphi, p1240_1]
                                  · have p1240_0 := h1240c.1
                                    have p1240_1 := h1240c.2.1
                                    have p1240_2 := h1240c.2.2.1
                                    have p1240_3 := h1240c.2.2.2
                                    linarith only [hlam, p1240_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1278 | h1278
                    · linarith only [h0, h1198, h1203, h1225, h1278, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1280 | h1280
                      · linarith only [h0, h1199, h1225, h1278, h1280, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1282 | h1282
                        · linarith only [h0, h1199, h1225, h1282, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1284 | h1284
                          · linarith only [h0, h1202, h1203, h1225, h1284, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1286 | h1286
                            · linarith only [h0, h1223, h1225, h1280, h1286, hc01, hlam, hphi, u1elo2]
                            · linarith only [h0, h1199, h1224, h1225, h1284, h1286, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1199, h1224, hlam]
              · linarith only [h0, h1202, h1223, hlam]
      · linarith only [h0, h1198, h1202, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1292 | h1292
    · linarith only [h0, h1292, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1294 | h1294
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1295 | h1295
        · linarith only [h1198, h1199, h1295, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1297 | h1297
          · linarith only [h0, h1198, h1297, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1300 | h1300
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1301 | h1301
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1302 | h1302
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1303 | h1303
                    · linarith only [h1198, h1199, h1295, h1301, h1303, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1305 | h1305
                      · linarith only [h1198, h1292, h1297, h1305, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1307 | h1307
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1308 | h1308
                          · linarith only [h0, h1292, h1294, h1303, h1307, h1308, hc01, hlam, hphi, u1elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1310 | h1310
                            · linarith only [h1198, h1292, h1300, h1305, h1310, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1312 | h1312
                              · linarith only [h1301, h1312, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1314 | h1314
                                · rcases h3bigk with h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c | h1315c
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1198, h1292, h1300, h1307, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1315_1, u1elo3]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1198, h1292, h1307, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1315_1, u1elo3]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1295, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1297, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1198, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1198, h1292, h1307, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1315_1, u1elo3]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1303, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1305, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1294, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1300, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1308, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1310, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1331 | h1331
                                    · linarith only [h1331, hlam, p1315_0]
                                    · rcases p1315_3 (m.d 1 3) (by simp) with h1333 | h1333
                                      · linarith only [h1303, h1333, hlam]
                                      · rcases p1315_3 (m.d 2 3) (by simp) with h1335 | h1335
                                        · linarith only [h1308, h1335, hlam]
                                        · rcases p1315_3 (m.d 3 4) (by simp) with h1337 | h1337
                                          · rcases p1315_3 (m.d 3 5) (by simp) with h1338 | h1338
                                            · linarith only [h1314, h1338, hlam]
                                            · linarith only [h1297, h1338, hlam]
                                          · linarith only [h1337, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1342 | h1342
                                    · linarith only [h1295, h1342, hlam]
                                    · linarith only [h1198, h1342, hlam]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1345 | h1345
                                    · linarith only [h1295, h1345, hlam]
                                    · linarith only [h1294, h1345, hlam]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1292, h1305, hc01, hc34, hlam, hphi, ht12, ht23, p1315_1]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1350 | h1350
                                    · linarith only [h1350, hlam, p1315_0]
                                    · rcases p1315_3 (m.d 1 3) (by simp) with h1352 | h1352
                                      · linarith only [h1305, h1352, hlam]
                                      · rcases p1315_3 (m.d 2 3) (by simp) with h1354 | h1354
                                        · linarith only [h1310, h1354, hlam]
                                        · rcases p1315_3 (m.d 3 4) (by simp) with h1356 | h1356
                                          · rcases p1315_3 (m.d 3 5) (by simp) with h1357 | h1357
                                            · rcases h5bigk with h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1292, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1292, hlam, hphi, ht01, ht0b, ht5b, p1358_1, u1elo4, u5ehi2]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1297, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1292, h1308, h1312, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1, u1elo4]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, hphi, ht01, ht0b, ht5b, p1358_1, u1elo4, u5ehi0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1302, hlam, hphi, ht01, ht0b, ht5b, p1358_1, u1elo1, u5ehi2]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1305, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1301, h1307, h1308, h1312, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1, u1elo1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1198, h1292, h1300, h1302, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1358_1, u1elo1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1302, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1310, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1312, hlam, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1198, h1292, h1300, hc23, hc35, hlam, hphi, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1198, h1292, h1300, hc23, hc35, hlam, hphi, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                rcases p1358_3 (m.d 0 5) (by simp) with h1376 | h1376
                                                · linarith only [h1297, h1376, hlam]
                                                · linarith only [h1198, h1292, h1300, h1314, h1376, hc23, hc34, hlam, hphi, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1308, h1312, h1314, hc23, hc34, hlam, hphi, p1358_1]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1299, hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1307, hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1299, hc04, hlam, hphi, ht0b, ht5b, p1358_1, u5ehi2]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [h1314, hlam, p1358_0]
                                              · have p1358_0 := h1358c.1
                                                have p1358_1 := h1358c.2.1
                                                have p1358_2 := h1358c.2.2.1
                                                have p1358_3 := h1358c.2.2.2
                                                linarith only [hlam, p1358_0]
                                            · linarith only [h1357, hlam, p1315_0]
                                          · linarith only [h1295, h1356, hlam]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1388 | h1388
                                    · linarith only [h1297, h1388, hlam]
                                    · linarith only [h1198, h1388, hlam]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    rcases p1315_3 (m.d 0 3) (by simp) with h1391 | h1391
                                    · linarith only [h1297, h1391, hlam]
                                    · linarith only [h1294, h1391, hlam]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [h1314, hlam, p1315_0]
                                  · have p1315_0 := h1315c.1
                                    have p1315_1 := h1315c.2.1
                                    have p1315_2 := h1315c.2.2.1
                                    have p1315_3 := h1315c.2.2.2
                                    linarith only [hlam, p1315_0]
                                · linarith only [h1199, h1295, h1299, h1301, h1314, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h1199, h1299, h1307, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1398 | h1398
                    · linarith only [h0, h1198, h1302, h1398, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1400 | h1400
                      · linarith only [h1198, h1400, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1402 | h1402
                        · linarith only [h1301, h1302, h1402, hlam]
                        · linarith only [h1199, h1299, h1402, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1405 | h1405
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1406 | h1406
                    · linarith only [h1198, h1292, h1405, h1406, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1408 | h1408
                      · linarith only [h1198, h1292, h1405, h1408, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1410 | h1410
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1411 | h1411
                          · linarith only [h1198, h1292, h1300, h1301, h1405, h1406, h1411, hlam]
                          · linarith only [h1198, h1292, h1300, h1301, h1405, h1411, hc23, hc34, hlam, hphi]
                        · linarith only [h1198, h1292, h1300, h1301, h1405, h1410, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1415 | h1415
                    · linarith only [h0, h1198, h1301, h1415, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1417 | h1417
                      · linarith only [h0, h1198, h1301, h1417, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1419 | h1419
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1420 | h1420
                          · linarith only [h0, h1198, h1300, h1405, h1415, h1419, h1420, hlam]
                          · linarith only [h0, h1198, h1300, h1301, h1420, hc23, hc34, hlam, hphi]
                        · linarith only [h1198, h1199, h1300, h1419, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1294, h1300, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1425 | h1425
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1426 | h1426
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1427 | h1427
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1428 | h1428
                    · linarith only [h1198, h1199, h1428, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1430 | h1430
                      · linarith only [h1198, h1292, h1427, h1430, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1432 | h1432
                        · linarith only [h1198, h1199, h1299, h1425, h1426, h1432, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                        · linarith only [h1198, h1199, h1425, h1432, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1435 | h1435
                    · linarith only [h1198, h1199, h1435, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1437 | h1437
                      · linarith only [h1198, h1199, h1437, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1439 | h1439
                        · linarith only [h1198, h1199, h1299, h1425, h1439, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1198, h1199, h1425, h1439, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1442 | h1442
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1443 | h1443
                    · linarith only [h0, h1198, h1443, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1445 | h1445
                      · linarith only [h1198, h1292, h1442, h1445, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1447 | h1447
                        · linarith only [h1199, h1299, h1447, hc01, hlam, hphi, u1elo3]
                        · linarith only [h1198, h1199, h1425, h1447, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
                    · linarith only [h0, h1198, h1426, h1450, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                      · linarith only [h1198, h1452, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1454 | h1454
                        · linarith only [h1198, h1199, h1299, h1425, h1454, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
                        · linarith only [h1198, h1199, h1425, h1454, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h1198, h1294, h1425, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · linarith only [h0, h1198, h1294, hlam]

end R2N4
