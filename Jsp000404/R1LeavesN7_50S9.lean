import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h986 | h986
  · rcases m.htr 0 2 5 (by decide) (by decide) with h987 | h987
    · rcases m.htr 0 3 4 (by decide) (by decide) with h988 | h988
      · rcases m.htr 0 3 5 (by decide) (by decide) with h989 | h989
        · rcases m.htr 0 4 5 (by decide) (by decide) with h990 | h990
          · rcases m.htr 1 2 3 (by decide) (by decide) with h991 | h991
            · linarith only [h0, h1, h991, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h993 | h993
              · rcases m.htr 1 3 4 (by decide) (by decide) with h994 | h994
                · rcases m.htr 1 3 5 (by decide) (by decide) with h995 | h995
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h996 | h996
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h997 | h997
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h998 | h998
                        · linarith only [h0, h1, h991, h993, h998, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h1, h991, h998, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h991, h993, h995, h997, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1003 | h1003
                        · linarith only [h0, h1, h1003, h991, h993, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h1, h1003, h991, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1002, h991, h993, h994, h996, hlam]
                  · linarith only [h0, h1, h993, h995, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h0, h1, h988, h993, h994, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1, h987, h991, h993, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1010 | h1010
            · linarith only [h0, h1, h1010, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1013 | h1013
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1014 | h1014
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                    · linarith only [h1, h1010, h1015, h986, h988, h990, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1017 | h1017
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1018 | h1018
                        · linarith only [h0, h1, h1010, h1012, h1018, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h0, h1, h1010, h1018, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1010, h1012, h1013, h1015, h1017, hlam]
                  · linarith only [h0, h1, h1014, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h1012, h1013, h988, h990, hc05, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1, h1010, h1012, h987, hc12, hc23, hlam, hphi]
        · linarith only [h988, h989, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1026 | h1026
        · linarith only [h1026, h988, hc34, hlam, hphi, u3ehi4]
        · linarith only [h0, h1, h1026, h987, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1029 | h1029
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1030 | h1030
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1031 | h1031
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
            · linarith only [h0, h1, h1032, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
              · linarith only [h0, h1, h1032, h1034, h987, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1037 | h1037
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1038 | h1038
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1040 | h1040
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1041 | h1041
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1042 | h1042
                            · rcases h5bigk with h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c | h1043c
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1, h1032, h1037, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1043_1, u3ehi4]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h987, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1, h1032, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1043_1, u3ehi4]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1, h1032, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1043_1]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h986, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1034, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1043_1, u3ehi4]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1, h1032, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1043_1]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h0, h987, hc12, hc25, hlam, hphi, p1043_1]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1034, hc12, hc25, hlam, hphi, p1043_1]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1040, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1043_1, u3ehi4]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                rcases p1043_3 (m.d 0 5) (by simp) with h1058 | h1058
                                · linarith only [h1058, h987, hlam]
                                · linarith only [h1031, h1058, hlam]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1030, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1037, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1040, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1, h1032, h1037, h986, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1043_1]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1031, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1038, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1041, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [h1042, hlam, p1043_0]
                              · have p1043_0 := h1043c.1
                                have p1043_1 := h1043c.2.1
                                have p1043_2 := h1043c.2.2.1
                                have p1043_3 := h1043c.2.2.2
                                linarith only [hlam, p1043_0]
                            · linarith only [h1, h1032, h1038, h1042, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1, h1032, h1038, h1039, h1041, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h1032, h1037, h1040, h986, hlam]
                      · linarith only [h1, h1032, h1037, h1039, h986, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1077 | h1077
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1078 | h1078
                            · linarith only [h1036, h1038, h1078, hlam]
                            · rcases h5bigk with h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c | h1080c
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1037, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1080_1, u3ehi4]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h987, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1, h1032, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1080_1, u3ehi4]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1, h1032, h1036, h1038, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1080_1, u3ehi3]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h986, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1034, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1080_1, u3ehi4]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1038, hlam, p1080_1]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h0, h1075, h1077, h987, hc12, hc23, hlam, hphi, p1080_1]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1034, h1075, h1077, hc12, hc23, hlam, hphi, p1080_1]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1075, h1077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1080_1, u3ehi4]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1036, h1038, h1075, h1077, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1080_1, u3ehi3]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1030, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1037, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1076, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1078, hlam, p1080_1]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1031, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1029, h1031, h1036, h1038, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1080_1, u3ehi3]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1077, hlam, p1080_0]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [h1, h1029, h1031, h1032, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1080_1, u3ehi4]
                              · have p1080_0 := h1080c.1
                                have p1080_1 := h1080c.2.1
                                have p1080_2 := h1080c.2.2.1
                                have p1080_3 := h1080c.2.2.2
                                linarith only [hlam, p1080_0]
                          · linarith only [h1031, h1077, h987, hlam]
                        · linarith only [h0, h1, h1032, h1076, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1029, h1031, h1032, h1036, h1038, h1075, hlam]
                  · linarith only [h0, h1, h1037, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h1030, h1036, h986, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
            · linarith only [h0, h1, h1111, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
              · linarith only [h0, h1113, h987, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1115 | h1115
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1116 | h1116
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
                    · linarith only [h1, h1029, h1031, h1111, h1117, h986, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1120 | h1120
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1121 | h1121
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1122 | h1122
                            · linarith only [h1029, h1031, h1122, hlam]
                            · rcases h5bigk with h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c | h1124c
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1, h1111, h1113, h986, hc12, hc23, hlam, hphi, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h987, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1122, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1031, hlam, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h986, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1113, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1122, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1117, hlam, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h0, h987, hc12, hc25, hlam, hphi, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1113, hc12, hc25, hlam, hphi, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1120, h1122, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1029, h1031, h1119, h1121, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1030, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1116, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1120, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1122, hlam, p1124_1]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1116, h1122, h986, hc45, hlam, hphi, ht34, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1116, h1122, hc45, hlam, hphi, ht34, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1121, hlam, p1124_0]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [h1119, h1121, h1122, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1124_1, u3ehi3]
                              · have p1124_0 := h1124c.1
                                have p1124_1 := h1124c.2.1
                                have p1124_2 := h1124c.2.2.1
                                have p1124_3 := h1124c.2.2.2
                                linarith only [hlam, p1124_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1150 | h1150
                            · linarith only [h0, h1, h1029, h1111, h1121, h1150, h987, hc12, hc23, hlam, hphi]
                            · rcases h5bigk with h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c | h1152c
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1115, h1117, h987, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u3ehi3]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h987, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1, h1111, h986, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1031, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h986, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1113, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1152_1, u3ehi4]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1117, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h987, hc12, hc25, hlam, hphi, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1113, hc12, hc25, hlam, hphi, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1120, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1152_1, u3ehi4]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1121, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1030, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1116, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1120, hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1150, hlam, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1115, h1117, h986, hc45, hlam, hphi, ht34, p1152_1, u3ehi3]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h1115, h1117, hc45, hlam, hphi, ht34, p1152_1, u3ehi3]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [h0, h987, hc12, hc45, hlam, hphi, ht23, ht34, p1152_1]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hc45, hlam, hphi, ht34, p1152_1, u3ehi4]
                              · have p1152_0 := h1152c.1
                                have p1152_1 := h1152c.2.1
                                have p1152_2 := h1152c.2.2.1
                                have p1152_3 := h1152c.2.2.2
                                linarith only [hlam, p1152_0]
                        · linarith only [h1, h1111, h1115, h1117, h1120, h986, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h1111, h1115, h1117, h1119, h986, hlam]
                  · linarith only [h0, h1, h1116, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h1115, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1029, h1030, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1183 | h1183
        · linarith only [h1029, h1183, hc34, hlam, hphi, u3ehi4]
        · linarith only [h1, h1183, h986, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1186 | h1186
    · linarith only [h0, h1186, h986, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1188 | h1188
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1189 | h1189
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1190 | h1190
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
            · linarith only [h0, h1, h1191, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
              · linarith only [h0, h1, h1186, h1191, h1193, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1195 | h1195
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1196 | h1196
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1197 | h1197
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1198 | h1198
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1199 | h1199
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1200 | h1200
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1201 | h1201
                            · rcases h5bigk with h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h986, hlam, p1202_1]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1186, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1188, h1190, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1202_1, u3ehi4]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                rcases p1202_3 (m.d 0 5) (by simp) with h1207 | h1207
                                · rcases p1202_3 (m.d 1 5) (by simp) with h1208 | h1208
                                  · rcases p1202_3 (m.d 2 5) (by simp) with h1209 | h1209
                                    · rcases p1202_3 (m.d 3 5) (by simp) with h1210 | h1210
                                      · linarith only [h1189, h1210, hlam]
                                      · linarith only [h1201, h1210, hlam]
                                    · linarith only [h1200, h1209, hlam]
                                  · linarith only [h1197, h1208, hlam]
                                · linarith only [h1190, h1207, hlam]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1191, h1195, h1197, h986, hc01, hc23, hlam, hphi, ht12, p1202_1]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1193, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1191, h1195, h1197, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1202_1, u3ehi4]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                rcases p1202_3 (m.d 0 5) (by simp) with h1220 | h1220
                                · linarith only [h1220, h986, hlam]
                                · linarith only [h1190, h1220, hlam]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h0, h1200, h986, hc12, hc24, hlam, hphi, p1202_1]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h0, h1200, h986, hc12, hc24, hlam, hphi, p1202_1]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1198, h1200, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1202_1, u3ehi4]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                rcases p1202_3 (m.d 0 5) (by simp) with h1227 | h1227
                                · linarith only [h1186, h1227, hlam]
                                · linarith only [h1190, h1227, hlam]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1189, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1196, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1199, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1, h1188, h1191, h1201, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1202_1]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1190, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1197, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1200, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [h1201, hlam, p1202_0]
                              · have p1202_0 := h1202c.1
                                have p1202_1 := h1202c.2.1
                                have p1202_2 := h1202c.2.2.1
                                have p1202_3 := h1202c.2.2.2
                                linarith only [hlam, p1202_0]
                            · rcases h5bigk with h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c | h1240c
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h986, hlam, p1240_1]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1186, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1, u3ehi4]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1201, h986, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1240_1]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h0, h986, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1240_1]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1193, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1193, h1198, h1200, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1240_1, u3ehi4]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1195, h1197, h1201, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1240_1, u3ehi3]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1190, h1198, h1200, h1201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1240_1, u3ehi3]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h0, h1198, h1200, h986, hc12, hc23, hlam, hphi, p1240_1]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1198, h1200, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1240_1, u3ehi4]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1198, h1200, h1201, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1240_1, u3ehi3]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1189, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1196, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1199, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1201, hlam, p1240_1]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1190, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1197, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1200, hlam, p1240_0]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [h1188, h1190, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1240_1, u3ehi4]
                              · have p1240_0 := h1240c.1
                                have p1240_1 := h1240c.2.1
                                have p1240_2 := h1240c.2.2.1
                                have p1240_3 := h1240c.2.2.2
                                linarith only [hlam, p1240_0]
                          · linarith only [h1186, h1190, h1200, hlam]
                        · linarith only [h0, h1, h1191, h1199, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1188, h1191, h1195, h1197, h1198, h986, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1190, h1197, h986, hlam]
                  · linarith only [h1, h1189, h1196, hlam]
                · linarith only [h1, h1189, h1195, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1272 | h1272
            · linarith only [h0, h1, h1272, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1274 | h1274
              · linarith only [h0, h1186, h1274, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1276 | h1276
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1277 | h1277
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1278 | h1278
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1279 | h1279
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1280 | h1280
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1281 | h1281
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1282 | h1282
                            · linarith only [h1188, h1190, h1282, hlam]
                            · rcases h5bigk with h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h986, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1186, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1190, h1272, h1276, h1278, h1282, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1190, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1272, h1276, h1278, h986, hc01, hc23, hlam, hphi, ht12, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1274, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1272, h1276, h1278, h1282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1284_1, u3ehi3]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1190, h1272, h1276, h1278, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h0, h1281, h986, hc12, hc24, hlam, hphi, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h0, h1281, h986, hc12, hc24, hlam, hphi, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1279, h1281, h1282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1284_1, u3ehi3]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1188, h1190, h1279, h1281, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1284_1, u3ehi3]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1189, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1277, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1280, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1282, hlam, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h0, h986, hc12, hc45, hlam, hphi, ht23, ht34, p1284_1]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1278, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1281, hlam, p1284_0]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [h1272, h1276, h1278, h1282, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1284_1, u3ehi3]
                              · have p1284_0 := h1284c.1
                                have p1284_1 := h1284c.2.1
                                have p1284_2 := h1284c.2.2.1
                                have p1284_3 := h1284c.2.2.2
                                linarith only [hlam, p1284_0]
                          · linarith only [h0, h1272, h1274, h1276, h1278, h1281, h986, hc12, hc23, hlam, hphi]
                        · linarith only [h1189, h1190, h1272, h1276, h1278, h1280, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h1272, h1279, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1313 | h1313
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1314 | h1314
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1315 | h1315
                          · linarith only [h0, h1278, h1315, h986, hc12, hc24, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1317 | h1317
                            · linarith only [h0, h1274, h1315, h1317, h986, hc12, hc34, hlam, hphi, ht23]
                            · rcases h5bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h986, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1186, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p1319_1, u3ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1190, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1274, h1315, h986, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1274, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1274, h1315, hc45, hlam, hphi, ht34, p1319_1, u3ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1278, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1190, h1315, hc04, hc45, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h1315, h986, hc12, hc45, hlam, hphi, ht23, ht34, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1315, hc45, hlam, hphi, ht34, p1319_1, u3ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1315, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1189, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1277, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1314, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1317, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1188, h1190, hc45, hlam, hphi, ht34, p1319_1, u3ehi3]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h986, hc12, hc45, hlam, hphi, ht23, ht34, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h1186, hc12, hc45, hlam, hphi, ht23, ht34, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hc45, hlam, hphi, ht34, p1319_1, u3ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                        · linarith only [h0, h1, h1272, h1314, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1272, h1277, h1313, h986, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h1189, h1277, hlam]
                · linarith only [h1, h1188, h1276, hlam]
        · linarith only [h1188, h1189, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1350 | h1350
        · linarith only [h1188, h1350, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1352 | h1352
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1353 | h1353
            · linarith only [h0, h1, h1353, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1355 | h1355
              · linarith only [h0, h1186, h1355, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1357 | h1357
                · linarith only [h0, h1, h1188, h1353, h1357, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1357, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
            · linarith only [h0, h1, h1360, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1362 | h1362
              · linarith only [h0, h1, h1186, h1188, h1352, h1362, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1364 | h1364
                · linarith only [h0, h1, h1188, h1360, h1364, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1, h1364, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x0 m hb2 hb3 hb5 h0 h1
  · exact r1l7_12_13_25_L_I_L_R_H_I_x0_x1 m hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1368 | h1368
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1369 | h1369
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1370 | h1370
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1371 | h1371
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1372 | h1372
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1374 | h1374
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
                · linarith only [h0, h1367, h1375, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1367, h1370, h1375, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h1367, h1370, h1374, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1367, h1370, h1373, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1380 | h1380
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1381 | h1381
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1382 | h1382
                · linarith only [h0, h1367, h1382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1367, h1370, h1380, h1382, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1367, h1380, h1381, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1370, h1380, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h1370, h1371, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1388 | h1388
        · linarith only [h1370, h1388, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1390 | h1390
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1391 | h1391
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1392 | h1392
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1393 | h1393
                · linarith only [h1367, h1370, h1393, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1395 | h1395
                  · linarith only [h1367, h1388, h1395, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1397 | h1397
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1398 | h1398
                      · linarith only [h1367, h1370, h1391, h1398, hlam]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1400 | h1400
                        · linarith only [h1367, h1388, h1391, h1400, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1402 | h1402
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                            · rcases h5bigk with h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h0, h1368, h1392, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h0, h1368, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1388, hlam, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h0, h1368, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1368, hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h0, h1368, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1395, hlam, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h0, h1368, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1369, hlam, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1392, hlam, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1400, hlam, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1369, hc02, hc45, hlam, hphi, ht0b, ht5b, p1404_1]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1368, h1391, h1395, h1403, hc34, hlam, hphi, p1404_1, u3ehi2]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1391, h1395, h1403, hc34, hlam, hphi, p1404_1, u3ehi2]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1400, h1403, hc34, hlam, hphi, p1404_1, u3ehi2]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                rcases p1404_3 (m.d 0 5) (by simp) with h1424 | h1424
                                · linarith only [h1388, h1424, hlam]
                                · linarith only [h1390, h1424, hlam]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1390, hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1397, hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1402, hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [h1403, hlam, p1404_0]
                              · have p1404_0 := h1404c.1
                                have p1404_1 := h1404c.2.1
                                have p1404_2 := h1404c.2.2.1
                                have p1404_3 := h1404c.2.2.2
                                linarith only [hlam, p1404_0]
                            · linarith only [h1370, h1403, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1370, h1390, h1398, h1402, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h1370, h1390, h1391, h1393, h1397, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h1367, h1391, h1392, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1391, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1437 | h1437
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1438 | h1438
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1439 | h1439
                · linarith only [h0, h1367, h1439, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1441 | h1441
                  · linarith only [h0, h1367, h1441, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1443 | h1443
                    · linarith only [h1370, h1390, h1439, h1443, hc34, hlam, hphi, u3ehi0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1445 | h1445
                      · linarith only [h0, h1368, h1437, h1439, h1443, h1445, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1447 | h1447
                        · linarith only [h0, h1368, h1437, h1439, h1443, h1447, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1449 | h1449
                          · linarith only [h1370, h1390, h1445, h1449, hc34, hlam, hphi, u3ehi0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1451 | h1451
                            · linarith only [h1367, h1370, h1390, h1437, h1451, hc34, hlam, hphi, u3ehi2]
                            · linarith only [h1367, h1370, h1437, h1451, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h1367, h1437, h1438, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1437, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · linarith only [h0, h1368, h1369, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1457 | h1457
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1458 | h1458
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1459 | h1459
        · linarith only [h1367, h1368, h1459, hlam]
        · linarith only [h1458, h1459, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1462 | h1462
        · linarith only [h1458, h1462, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1464 | h1464
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1465 | h1465
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1466 | h1466
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1467 | h1467
                · linarith only [h1367, h1458, h1467, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1469 | h1469
                  · linarith only [h1367, h1368, h1466, h1469, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h1367, h1368, h1469, hc35, hlam, hphi, u3ehi1]
              · linarith only [h0, h1457, h1466, hlam]
            · linarith only [h0, h1367, h1465, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1474 | h1474
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1475 | h1475
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1476 | h1476
                · linarith only [h1367, h1458, h1476, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1478 | h1478
                  · linarith only [h1367, h1368, h1475, h1478, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h1367, h1368, h1474, h1478, hc35, hlam, hphi, u3ehi2]
              · linarith only [h0, h1367, h1457, h1474, h1475, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1474, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1483 | h1483
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1484 | h1484
        · linarith only [h1367, h1368, h1484, hlam]
        · linarith only [h1483, h1484, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1487 | h1487
        · linarith only [h1483, h1487, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1489 | h1489
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1490 | h1490
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1491 | h1491
              · linarith only [h0, h1367, h1457, h1490, h1491, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1367, h1490, h1491, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1490, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1495 | h1495
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1496 | h1496
              · linarith only [h0, h1367, h1457, h1495, h1496, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1367, h1495, h1496, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h1367, h1495, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]

set_option maxHeartbeats 5348000 in
set_option maxHeartbeats 5348000 in
theorem r1l7_12_13_25_L_I_L_R_H_I_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1367 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1500 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1501 | h1501
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1502 | h1502
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1503 | h1503
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1504 | h1504
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1505 | h1505
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1506 | h1506
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1507 | h1507
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1508 | h1508
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1510 | h1510
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1511 | h1511
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1512 | h1512
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1513 | h1513
                          · rcases h5bigk with h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1500, h1506, h1511, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, h1511, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1500, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1511, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, h1505, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, h1505, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1501, hlam, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1506, hlam, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1514_1, u3ehi4]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1500, h1505, h1506, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1503, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1508, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1511, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1367, h1503, h1505, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1514_1]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1504, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1509, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1512, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [h1513, hlam, p1514_0]
                            · have p1514_0 := h1514c.1
                              have p1514_1 := h1514c.2.1
                              have p1514_2 := h1514c.2.2.1
                              have p1514_3 := h1514c.2.2.2
                              linarith only [hlam, p1514_0]
                          · linarith only [h1367, h1500, h1505, h1509, h1513, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1367, h1500, h1505, h1509, h1510, h1512, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1367, h1500, h1505, h1508, h1511, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1543 | h1543
                      · linarith only [h1510, h1543, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1367, h1500, h1505, h1508, h1543, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1547 | h1547
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1548 | h1548
                        · linarith only [h1505, h1507, h1509, h1546, h1548, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1550 | h1550
                          · linarith only [h1507, h1509, h1550, hlam]
                          · rcases h5bigk with h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c | h1552c
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1500, h1505, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1500, h1505, h1547, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1500, h1505, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1500, h1505, h1507, h1509, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi3]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1500, hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1547, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1500, h1505, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1509, hlam, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1501, hlam, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1506, hlam, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1548, hlam, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1503, hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1508, hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1547, hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1550, hlam, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1504, hlam, p1552_0]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1502, h1504, h1505, h1506, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1552_1]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1502, h1504, h1505, h1547, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [h1367, h1502, h1504, h1505, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1552_1, u3ehi4]
                            · have p1552_0 := h1552c.1
                              have p1552_1 := h1552c.2.1
                              have p1552_2 := h1552c.2.2.1
                              have p1552_3 := h1552c.2.2.2
                              linarith only [hlam, p1552_0]
                      · linarith only [h1367, h1500, h1505, h1508, h1547, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1367, h1502, h1504, h1505, h1507, h1509, h1546, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h1367, h1502, h1508, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1367, h1502, h1507, hlam]
            · linarith only [h0, h1501, h1506, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1583 | h1583
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1584 | h1584
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1585 | h1585
                · linarith only [h0, h1500, h1505, h1585, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1367, h1502, h1585, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1500, h1502, h1503, h1505, h1584, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
            · linarith only [h0, h1501, h1583, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1590 | h1590
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1591 | h1591
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1592 | h1592
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1593 | h1593
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1594 | h1594
                  · linarith only [h0, h1500, h1502, h1504, h1594, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1596 | h1596
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1597 | h1597
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1598 | h1598
                        · linarith only [h1502, h1504, h1590, h1596, h1598, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1600 | h1600
                          · linarith only [h1502, h1504, h1600, hlam]
                          · rcases h5bigk with h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c | h1602c
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1367, h1500, h1590, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1367, h1500, h1590, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1367, h1500, h1590, h1600, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1504, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1500, hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1367, h1500, h1590, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1367, h1500, h1590, h1600, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1594, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1501, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1591, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1600, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1598, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1503, hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1593, hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1597, hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [hlam, p1602_0]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1600, hlam, p1602_1]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1503, h1600, hc45, hlam, hphi, ht34, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1593, h1600, hc45, hlam, hphi, ht34, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1597, h1600, hc45, hlam, hphi, ht34, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [h1600, hc45, hlam, hphi, ht34, p1602_1, u3ehi3]
                            · have p1602_0 := h1602c.1
                              have p1602_1 := h1602c.2.1
                              have p1602_2 := h1602c.2.2.1
                              have p1602_3 := h1602c.2.2.2
                              linarith only [hlam, p1602_0]
                      · linarith only [h1367, h1500, h1590, h1593, h1597, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1502, h1504, h1596, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h1367, h1502, h1593, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1367, h1502, h1504, h1592, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h1501, h1591, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1633 | h1633
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1634 | h1634
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1635 | h1635
                · linarith only [h0, h1500, h1590, h1635, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h1500, h1502, h1504, h1590, h1635, hc35, hlam, hphi, u3ehi3]
              · linarith only [h0, h1500, h1502, h1504, h1590, h1634, hlam]
            · linarith only [h0, h1501, h1633, hlam]
      · linarith only [h1502, h1503, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1641 | h1641
      · linarith only [h1502, h1641, hc34, hlam, hphi, u3ehi4]
      · linarith only [h1367, h1500, h1641, hlam]
  · linarith only [h0, h1500, h1501, hlam]

end R2N4
