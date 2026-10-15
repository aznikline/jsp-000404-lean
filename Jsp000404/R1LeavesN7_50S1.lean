import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_50S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h978 | h978
  · rcases m.htr 0 2 4 (by decide) (by decide) with h979 | h979
    · rcases m.htr 0 2 5 (by decide) (by decide) with h980 | h980
      · linarith only [h0, h1, h980, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h982 | h982
        · rcases m.htr 0 3 5 (by decide) (by decide) with h983 | h983
          · linarith only [h0, h1, h978, h983, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h985 | h985
            · linarith only [h982, h983, h985, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
              · linarith only [h0, h1, h983, h987, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h1, h978, h983, h987, hc12, hlam, hphi, ht23, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h990 | h990
          · linarith only [h982, h990, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
            · linarith only [h0, h1, h979, h992, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
              · linarith only [h0, h1, h990, h994, hc23, hlam, hphi, u3elo4]
              · linarith only [h0, h1, h978, h990, h994, hc12, hlam, hphi, ht23, u3elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h997 | h997
      · linarith only [h0, h1, h997, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h999 | h999
        · linarith only [h978, h979, h999, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1001 | h1001
          · linarith only [h1001, h999, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1003 | h1003
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1004 | h1004
              · linarith only [h0, h1, h1003, h1004, h999, hc23, hlam, hphi, u3elo3]
              · linarith only [h0, h1, h1003, h1004, h978, h999, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1007 | h1007
              · linarith only [h0, h1, h1001, h1007, hc23, hlam, hphi, u3elo4]
              · linarith only [h1007, h978, h979, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1010 | h1010
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1011 | h1011
      · linarith only [h1011, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1013 | h1013
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1014 | h1014
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1015 | h1015
            · linarith only [h1010, h1015, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
              · linarith only [h0, h1, h1014, h1017, h978, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1019 | h1019
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1020 | h1020
                  · linarith only [h0, h1, h1011, h1014, h1020, h978, hc02, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1022 | h1022
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1023 | h1023
                      · linarith only [h0, h1, h1019, h1023, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h1014, h1023, h978, hc13, hlam, hphi, u3elo2]
                    · linarith only [h1013, h1017, h1019, h1022, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h1010, h1019, h978, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1028 | h1028
            · linarith only [h1010, h1014, h1028, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1030 | h1030
              · linarith only [h0, h1014, h1030, h978, hc23, hlam, hphi, u3elo4]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1032 | h1032
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1033 | h1033
                  · linarith only [h0, h1014, h1033, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1035 | h1035
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
                      · linarith only [h0, h1014, h1032, h1036, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                      · linarith only [h0, h1, h1032, h1036, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                    · linarith only [h1013, h1035, hc13, hlam, hphi, u3elo0]
                · linarith only [h1010, h1014, h1032, h978, hc12, hlam, hphi, ht23, u3elo4]
        · linarith only [h1010, h1013, h978, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1042 | h1042
      · linarith only [h1042, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1044 | h1044
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1045 | h1045
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1046 | h1046
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1047 | h1047
              · linarith only [h0, h1, h1047, h978, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1049 | h1049
                · linarith only [h0, h1, h1010, h1046, h1049, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1051 | h1051
                  · linarith only [h0, h1, h1044, h1046, h1051, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1054 | h1054
                      · linarith only [h0, h1, h1054, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1045, h1054, h978, hc13, hlam, hphi, u3elo2]
                    · linarith only [h1044, h1047, h1053, h978, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1058 | h1058
              · linarith only [h0, h1, h1045, h1058, h978, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1060 | h1060
                · linarith only [h0, h1010, h1060, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1062 | h1062
                  · linarith only [h0, h1, h1045, h1062, h978, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1064 | h1064
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1065 | h1065
                      · linarith only [h0, h1, h1065, hc12, hlam, hphi, ht23, u3elo1]
                      · linarith only [h1045, h1065, h978, hc13, hlam, hphi, u3elo2]
                    · linarith only [h1044, h1058, h1064, h978, hc12, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1069 | h1069
            · linarith only [h1044, h1045, h1069, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
              · linarith only [h0, h1071, h978, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1073 | h1073
                · linarith only [h0, h1010, h1073, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
                  · linarith only [h0, h1, h1075, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1077 | h1077
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1078 | h1078
                      · linarith only [h1010, h1044, h1045, h1078, hc02, hlam, hphi, ht23, u3elo1]
                      · linarith only [h0, h1, h1078, hc12, hlam, hphi, ht23, u3elo4]
                    · linarith only [h1044, h1045, h1077, hc13, hlam, hphi, u3elo4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1082 | h1082
          · linarith only [h1044, h1082, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1084 | h1084
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1085 | h1085
              · linarith only [h0, h1085, h978, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1087 | h1087
                · linarith only [h0, h1, h1010, h1084, h1087, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
                  · linarith only [h0, h1, h1042, h1089, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1091 | h1091
                    · linarith only [h1044, h1091, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1093 | h1093
                      · linarith only [h0, h1082, h1091, h1093, h978, hc12, hlam, hphi, ht23, u3elo3]
                      · linarith only [h0, h1, h1093, hc12, hlam, hphi, ht23, u3elo4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1096 | h1096
              · linarith only [h0, h1096, h978, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1098 | h1098
                · linarith only [h0, h1010, h1098, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1100 | h1100
                  · linarith only [h0, h1, h1100, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1102 | h1102
                    · linarith only [h0, h1044, h1102, h978, hc12, hlam, hphi, ht23, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1104 | h1104
                      · linarith only [h1102, h1104, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · linarith only [h0, h1, h1104, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0_x0 m hb0 hb2 hb3 hb5 h0 h1
  · exact r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x0_x1 m hb0 hb2 hb3 hb5 h0 h1

set_option maxHeartbeats 5456000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_0_M_IR_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1107 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1108 | h1108
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1109 | h1109
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1110 | h1110
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1111 | h1111
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1112 | h1112
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1113 | h1113
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1115 | h1115
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1116 | h1116
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1117 | h1117
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1118 | h1118
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1121 | h1121
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1122 | h1122
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1123 | h1123
                                · linarith only [h1108, h1120, h1123, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases h0emin with h1125 | h1125 | h1125 | h1125 | h1125
                                  · linarith only [h0, h1125, hc12, hlam, ht01]
                                  · rcases h2bigk with h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c | h1127c
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h0, hlam, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h0, h1120, h1122, h1123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h0, h1122, h1123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      rcases p1127_3 (m.d 0 2) (by simp) with h1132 | h1132
                                      · rcases p1127_3 (m.d 1 2) (by simp) with h1133 | h1133
                                        · rcases p1127_3 (m.d 2 3) (by simp) with h1134 | h1134
                                          · linarith only [h1108, h1134, hlam]
                                          · linarith only [h1121, h1134, hlam]
                                        · linarith only [h1116, h1133, hlam]
                                      · linarith only [h1132, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1125, hc12, hlam, ht01, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1120, h1122, h1123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1122, h1123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      rcases p1127_3 (m.d 0 2) (by simp) with h1143 | h1143
                                      · linarith only [h0, h1143, hlam]
                                      · linarith only [h1110, h1143, hlam]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1108, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1114, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1108, h1122, h1123, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1108, h1122, h1123, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1127_1, u3elo0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1109, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1115, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1120, hlam, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h0, h1109, h1122, h1123, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1110, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1116, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1121, hlam, p1127_1]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [h1122, hlam, p1127_0]
                                    · have p1127_0 := h1127c.1
                                      have p1127_1 := h1127c.2.1
                                      have p1127_2 := h1127c.2.2.1
                                      have p1127_3 := h1127c.2.2.2
                                      linarith only [hlam, p1127_0]
                                  · linarith only [h1125, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1111, h1125, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h0, h1107, h1125, hc12, hlam, ht01]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1164 | h1164
                                · linarith only [h1111, h1122, h1164, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h0emin with h1166 | h1166 | h1166 | h1166 | h1166
                                  · linarith only [h0, h1166, hc12, hlam, ht01]
                                  · rcases h2bigk with h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c | h1168c
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h0, hlam, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h0, h1121, hc12, hlam, hphi, ht01, ht0b, ht5b, p1168_1, u5ehi3]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      rcases p1168_3 (m.d 0 2) (by simp) with h1172 | h1172
                                      · rcases p1168_3 (m.d 1 2) (by simp) with h1173 | h1173
                                        · rcases p1168_3 (m.d 2 3) (by simp) with h1174 | h1174
                                          · linarith only [h1108, h1174, hlam]
                                          · linarith only [h1120, h1174, hlam]
                                        · linarith only [h1115, h1173, hlam]
                                      · linarith only [h1172, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      rcases p1168_3 (m.d 0 2) (by simp) with h1179 | h1179
                                      · rcases p1168_3 (m.d 1 2) (by simp) with h1180 | h1180
                                        · rcases p1168_3 (m.d 2 3) (by simp) with h1181 | h1181
                                          · linarith only [h1108, h1181, hlam]
                                          · linarith only [h1121, h1181, hlam]
                                        · linarith only [h1116, h1180, hlam]
                                      · linarith only [h1179, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1166, hc12, hlam, ht01, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1121, hc12, hlam, hphi, ht01, ht0b, ht5b, p1168_1, u5ehi3]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h0, h1107, h1119, h1122, hlam, p1168_2]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      rcases p1168_3 (m.d 0 2) (by simp) with h1190 | h1190
                                      · linarith only [h0, h1190, hlam]
                                      · linarith only [h1110, h1190, hlam]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1108, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1114, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      rcases p1168_3 (m.d 0 2) (by simp) with h1196 | h1196
                                      · rcases p1168_3 (m.d 1 2) (by simp) with h1197 | h1197
                                        · rcases p1168_3 (m.d 2 3) (by simp) with h1198 | h1198
                                          · rcases p1168_3 (m.d 2 4) (by simp) with h1199 | h1199
                                            · linarith only [h1120, h1199, hlam]
                                            · rcases p1168_3 (m.d 2 5) (by simp) with h1201 | h1201
                                              · linarith only [h1121, h1201, hlam]
                                              · linarith only [h1122, h1201, hlam]
                                          · linarith only [h1120, h1198, hlam]
                                        · linarith only [h1115, h1197, hlam]
                                      · linarith only [h1109, h1196, hlam]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1108, h1121, hc02, hlam, hphi, ht0b, ht5b, p1168_1, u5ehi3]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1109, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1115, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1120, hlam, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1122, hlam, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1110, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1116, hlam, p1168_0]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h1121, hlam, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [h0, h1107, h1116, h1120, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1168_1]
                                    · have p1168_0 := h1168c.1
                                      have p1168_1 := h1168c.2.1
                                      have p1168_2 := h1168c.2.2.1
                                      have p1168_3 := h1168c.2.2.2
                                      linarith only [hlam, p1168_0]
                                  · linarith only [h1166, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1111, h1166, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h0, h1107, h1166, hc12, hlam, ht01]
                            · linarith only [h1112, h1121, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1111, h1120, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1223 | h1223
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1224 | h1224
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1225 | h1225
                              · linarith only [h1115, h1119, h1225, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1227 | h1227
                                · linarith only [h1111, h1119, h1227, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                · rcases h0emin with h1229 | h1229 | h1229 | h1229 | h1229
                                  · linarith only [h0, h1229, hc12, hlam, ht01]
                                  · rcases h2bigk with h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c | h1231c
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h0, hlam, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h0, h1224, hc12, hlam, hphi, ht01, ht0b, ht5b, p1231_1, u5ehi3]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 2) (by simp) with h1235 | h1235
                                      · rcases p1231_3 (m.d 1 2) (by simp) with h1236 | h1236
                                        · rcases p1231_3 (m.d 2 3) (by simp) with h1237 | h1237
                                          · linarith only [h1108, h1237, hlam]
                                          · linarith only [h1223, h1237, hlam]
                                        · linarith only [h1115, h1236, hlam]
                                      · linarith only [h1235, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 2) (by simp) with h1242 | h1242
                                      · rcases p1231_3 (m.d 1 2) (by simp) with h1243 | h1243
                                        · rcases p1231_3 (m.d 2 3) (by simp) with h1244 | h1244
                                          · linarith only [h1108, h1244, hlam]
                                          · linarith only [h1224, h1244, hlam]
                                        · linarith only [h1116, h1243, hlam]
                                      · linarith only [h1242, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1229, hc12, hlam, ht01, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1224, hc12, hlam, hphi, ht01, ht0b, ht5b, p1231_1, u5ehi3]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 2) (by simp) with h1252 | h1252
                                      · linarith only [h0, h1252, hlam]
                                      · linarith only [h1109, h1252, hlam]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 2) (by simp) with h1255 | h1255
                                      · linarith only [h0, h1255, hlam]
                                      · linarith only [h1110, h1255, hlam]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1108, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1114, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      rcases p1231_3 (m.d 0 2) (by simp) with h1261 | h1261
                                      · rcases p1231_3 (m.d 1 2) (by simp) with h1262 | h1262
                                        · rcases p1231_3 (m.d 2 3) (by simp) with h1263 | h1263
                                          · rcases p1231_3 (m.d 2 4) (by simp) with h1264 | h1264
                                            · linarith only [h1223, h1264, hlam]
                                            · rcases p1231_3 (m.d 2 5) (by simp) with h1266 | h1266
                                              · linarith only [h1224, h1266, hlam]
                                              · linarith only [h1225, h1266, hlam]
                                          · linarith only [h1223, h1263, hlam]
                                        · linarith only [h1115, h1262, hlam]
                                      · linarith only [h1109, h1261, hlam]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1108, h1224, hc02, hlam, hphi, ht0b, ht5b, p1231_1, u5ehi3]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1109, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1115, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1223, hlam, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1225, hlam, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1110, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1116, hlam, p1231_0]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h1224, hlam, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [h0, h1107, h1116, h1223, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1231_1]
                                    · have p1231_0 := h1231c.1
                                      have p1231_1 := h1231c.2.1
                                      have p1231_2 := h1231c.2.2.1
                                      have p1231_3 := h1231c.2.2.2
                                      linarith only [hlam, p1231_0]
                                  · linarith only [h1229, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1111, h1229, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h0, h1107, h1229, hc12, hlam, ht01]
                            · linarith only [h1112, h1224, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1111, h1223, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1112, h1118, hc13, hlam, hphi, u3elo0]
                    · linarith only [h1111, h1114, h1117, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h1107, h1116, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1115, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1107, h1114, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1293 | h1293
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1294 | h1294
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1295 | h1295
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1296 | h1296
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1297 | h1297
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1298 | h1298
                        · linarith only [h1107, h1113, h1298, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1300 | h1300
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1301 | h1301
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1302 | h1302
                              · linarith only [h1109, h1113, h1302, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1304 | h1304
                                · linarith only [h1109, h1113, h1300, h1304, hlam]
                                · rcases h0emin with h1306 | h1306 | h1306 | h1306 | h1306
                                  · linarith only [h0, h1306, hc12, hlam, ht01]
                                  · rcases h2bigk with h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h0, hlam, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1301, hc02, hlam, hphi, ht0b, ht5b, p1308_1, u5ehi3]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      rcases p1308_3 (m.d 0 2) (by simp) with h1312 | h1312
                                      · rcases p1308_3 (m.d 1 2) (by simp) with h1313 | h1313
                                        · rcases p1308_3 (m.d 2 3) (by simp) with h1314 | h1314
                                          · linarith only [h1108, h1314, hlam]
                                          · linarith only [h1300, h1314, hlam]
                                        · linarith only [h1294, h1313, hlam]
                                      · linarith only [h1312, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      rcases p1308_3 (m.d 0 2) (by simp) with h1319 | h1319
                                      · rcases p1308_3 (m.d 1 2) (by simp) with h1320 | h1320
                                        · rcases p1308_3 (m.d 2 3) (by simp) with h1321 | h1321
                                          · linarith only [h1108, h1321, hlam]
                                          · linarith only [h1301, h1321, hlam]
                                        · linarith only [h1295, h1320, hlam]
                                      · linarith only [h1319, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1306, hc12, hlam, ht01, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1301, hc12, hlam, hphi, ht01, ht0b, ht5b, p1308_1, u5ehi3]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      rcases p1308_3 (m.d 0 2) (by simp) with h1329 | h1329
                                      · linarith only [h0, h1329, hlam]
                                      · linarith only [h1109, h1329, hlam]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      rcases p1308_3 (m.d 0 2) (by simp) with h1332 | h1332
                                      · linarith only [h0, h1332, hlam]
                                      · linarith only [h1110, h1332, hlam]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1108, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1293, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      rcases p1308_3 (m.d 0 2) (by simp) with h1338 | h1338
                                      · rcases p1308_3 (m.d 1 2) (by simp) with h1339 | h1339
                                        · rcases p1308_3 (m.d 2 3) (by simp) with h1340 | h1340
                                          · rcases p1308_3 (m.d 2 4) (by simp) with h1341 | h1341
                                            · linarith only [h1300, h1341, hlam]
                                            · rcases p1308_3 (m.d 2 5) (by simp) with h1343 | h1343
                                              · linarith only [h1301, h1343, hlam]
                                              · linarith only [h1302, h1343, hlam]
                                          · linarith only [h1300, h1340, hlam]
                                        · linarith only [h1294, h1339, hlam]
                                      · linarith only [h1109, h1338, hlam]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1108, hc02, hlam, hphi, ht0b, ht5b, p1308_1, u5ehi2]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1109, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1294, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1300, hlam, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1302, hlam, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1110, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1295, hlam, p1308_0]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h1301, hlam, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [h0, h1107, h1295, h1300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1308_1]
                                    · have p1308_0 := h1308c.1
                                      have p1308_1 := h1308c.2.1
                                      have p1308_2 := h1308c.2.2.1
                                      have p1308_3 := h1308c.2.2.2
                                      linarith only [hlam, p1308_0]
                                  · linarith only [h1306, hlam, ht01, ht12, ht23, u3elo0]
                                  · linarith only [h1113, h1306, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h0, h1107, h1306, hc12, hlam, ht01]
                            · linarith only [h1112, h1301, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1111, h1300, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1112, h1297, hc13, hlam, hphi, u3elo0]
                    · linarith only [h1111, h1293, h1296, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h1107, h1295, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1294, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1293, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1370 | h1370
            · linarith only [h1111, h1112, h1370, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1373 | h1373
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1374 | h1374
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1376 | h1376
                      · linarith only [h1112, h1376, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1378 | h1378
                        · linarith only [h0, h1107, h1370, h1375, h1376, h1378, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1380 | h1380
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1381 | h1381
                            · linarith only [h1108, h1376, h1381, hc13, hlam, hphi, u3elo0]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1383 | h1383
                              · linarith only [h1109, h1111, h1112, h1378, h1383, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1385 | h1385
                                · linarith only [h1111, h1112, h1370, h1385, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases h0emin with h1387 | h1387 | h1387 | h1387 | h1387
                                  · linarith only [h0, h1387, hc12, hlam, ht01]
                                  · rcases h2bigk with h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c | h1389c
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h0, hlam, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1392 | h1392
                                      · rcases p1389_3 (m.d 1 2) (by simp) with h1393 | h1393
                                        · rcases p1389_3 (m.d 2 3) (by simp) with h1394 | h1394
                                          · linarith only [h1394, hlam, p1389_0]
                                          · rcases p1389_3 (m.d 2 4) (by simp) with h1396 | h1396
                                            · linarith only [h1109, h1396, hlam]
                                            · rcases p1389_3 (m.d 2 5) (by simp) with h1398 | h1398
                                              · linarith only [h1110, h1398, hlam]
                                              · linarith only [h1381, h1398, hlam]
                                        · linarith only [h1372, h1393, hlam]
                                      · linarith only [h1392, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1403 | h1403
                                      · rcases p1389_3 (m.d 1 2) (by simp) with h1404 | h1404
                                        · rcases p1389_3 (m.d 2 3) (by simp) with h1405 | h1405
                                          · linarith only [h1108, h1405, hlam]
                                          · linarith only [h1380, h1405, hlam]
                                        · linarith only [h1373, h1404, hlam]
                                      · linarith only [h1403, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1410 | h1410
                                      · rcases p1389_3 (m.d 1 2) (by simp) with h1411 | h1411
                                        · rcases p1389_3 (m.d 2 3) (by simp) with h1412 | h1412
                                          · linarith only [h1108, h1412, hlam]
                                          · rcases p1389_3 (m.d 2 4) (by simp) with h1414 | h1414
                                            · linarith only [h1109, h1414, hlam]
                                            · rcases p1389_3 (m.d 2 5) (by simp) with h1416 | h1416
                                              · linarith only [h1416, hlam, p1389_0]
                                              · rcases h2emin with h1418 | h1418 | h1418 | h1418 | h1418
                                                · rcases h5bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, p1419_0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1419_1, u5ehi1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1419_1, u5ehi2]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1112, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1370, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1107, hlam, p1419_0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, p1419_0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1419_1, u5ehi2]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1376, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1378, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1110, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1374, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, p1419_0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1381, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1383, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1419_1, u3elo4, u5ehi0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1374, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1419_1, u3elo4, u5ehi2]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1419_1, u3elo4, u5ehi2]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, p1419_0]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1385, hlam, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1107, h1372, h1376, h1380, hc34, hc45, hlam, hphi, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1372, h1376, h1380, hc34, hc45, hlam, hphi, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1380, h1381, hc34, hc45, hlam, hphi, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [h1108, h1112, h1380, hc34, hc45, hlam, hphi, p1419_1]
                                                  · have p1419_0 := h1419c.1
                                                    have p1419_1 := h1419c.2.1
                                                    have p1419_2 := h1419c.2.2.1
                                                    have p1419_3 := h1419c.2.2.2
                                                    linarith only [hlam, p1419_0]
                                                · rcases h5bigk with h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, p1445_0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h0, h1107, h1372, h1376, h1380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h0, h1107, h1380, h1381, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1112, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1370, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1107, hlam, p1445_0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, p1445_0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h0, h1107, h1380, h1381, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1376, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1378, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1110, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1374, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, p1445_0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1381, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1383, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1445_1, u3elo4, u5ehi0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1374, h1380, h1381, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1445_1, u3elo4]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1380, h1381, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1445_1, u3elo4]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, p1445_0]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1385, hlam, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1107, h1374, h1380, h1381, hc34, hc45, hlam, hphi, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1374, h1380, h1381, hc34, hc45, hlam, hphi, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1380, h1381, hc34, hc45, hlam, hphi, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [h1108, h1112, h1380, hc34, hc45, hlam, hphi, p1445_1]
                                                  · have p1445_0 := h1445c.1
                                                    have p1445_1 := h1445c.2.1
                                                    have p1445_2 := h1445c.2.2.1
                                                    have p1445_3 := h1445c.2.2.2
                                                    linarith only [hlam, p1445_0]
                                                · linarith only [h1381, h1418, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1389_1]
                                                · linarith only [h1109, h1111, h1418, hlam, ht23, u3elo0]
                                                · linarith only [h0, h1418, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1389_1]
                                        · linarith only [h1374, h1411, hlam]
                                      · linarith only [h1410, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1387, hc12, hlam, ht01, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1478 | h1478
                                      · linarith only [h0, h1478, hlam]
                                      · linarith only [h1108, h1478, hlam]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1481 | h1481
                                      · linarith only [h0, h1481, hlam]
                                      · linarith only [h1109, h1481, hlam]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      rcases p1389_3 (m.d 0 2) (by simp) with h1484 | h1484
                                      · linarith only [h0, h1484, hlam]
                                      · linarith only [h1110, h1484, hlam]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1108, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1372, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1108, h1112, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1389_1, u3elo4]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1381, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1109, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1373, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1380, hlam, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1383, hlam, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1110, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1374, hlam, p1389_0]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h1110, h1380, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [h0, h1107, h1374, h1380, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1389_1]
                                    · have p1389_0 := h1389c.1
                                      have p1389_1 := h1389c.2.1
                                      have p1389_2 := h1389c.2.2.1
                                      have p1389_3 := h1389c.2.2.2
                                      linarith only [hlam, p1389_0]
                                  · linarith only [h1112, h1387, hlam, ht01, ht12, ht23, u3elo4]
                                  · linarith only [h1111, h1112, h1387, hlam, ht01, ht12, ht23, u3elo4]
                                  · linarith only [h0, h1107, h1387, hc12, hlam, ht01]
                          · linarith only [h1111, h1112, h1380, hc23, hlam, hphi, u3elo4]
                    · linarith only [h1111, h1112, h1372, h1375, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1107, h1374, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1373, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1107, h1372, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1510 | h1510
          · linarith only [h1111, h1510, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1512 | h1512
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1513 | h1513
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1514 | h1514
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1515 | h1515
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1516 | h1516
                    · linarith only [h1111, h1516, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1518 | h1518
                      · linarith only [h1510, h1516, h1518, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1520 | h1520
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1521 | h1521
                          · linarith only [h1108, h1111, h1521, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1523 | h1523
                            · linarith only [h1108, h1510, h1523, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1525 | h1525
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1526 | h1526
                                · rcases h0emin with h1527 | h1527 | h1527 | h1527 | h1527
                                  · linarith only [h0, h1527, hc12, hlam, ht01]
                                  · rcases h2bigk with h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c | h1529c
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h0, hlam, p1529_1]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      rcases p1529_3 (m.d 0 2) (by simp) with h1532 | h1532
                                      · rcases p1529_3 (m.d 1 2) (by simp) with h1533 | h1533
                                        · rcases p1529_3 (m.d 2 3) (by simp) with h1534 | h1534
                                          · linarith only [h1534, hlam, p1529_0]
                                          · rcases p1529_3 (m.d 2 4) (by simp) with h1536 | h1536
                                            · linarith only [h1109, h1536, hlam]
                                            · linarith only [h1521, h1536, hlam]
                                        · linarith only [h1513, h1533, hlam]
                                      · linarith only [h1532, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1525, hc02, hlam, hphi, ht0b, ht5b, p1529_1, u5ehi4]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      rcases p1529_3 (m.d 0 2) (by simp) with h1542 | h1542
                                      · rcases p1529_3 (m.d 1 2) (by simp) with h1543 | h1543
                                        · rcases p1529_3 (m.d 2 3) (by simp) with h1544 | h1544
                                          · linarith only [h1108, h1544, hlam]
                                          · rcases p1529_3 (m.d 2 4) (by simp) with h1546 | h1546
                                            · linarith only [h1109, h1546, hlam]
                                            · linarith only [h1525, h1546, hlam]
                                        · linarith only [h1515, h1543, hlam]
                                      · linarith only [h1542, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1527, hc12, hlam, ht01, p1529_1]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      rcases p1529_3 (m.d 0 2) (by simp) with h1553 | h1553
                                      · linarith only [h0, h1553, hlam]
                                      · linarith only [h1108, h1553, hlam]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1525, hc12, hlam, hphi, ht01, ht0b, ht5b, p1529_1, u5ehi4]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      rcases p1529_3 (m.d 0 2) (by simp) with h1557 | h1557
                                      · linarith only [h0, h1557, hlam]
                                      · linarith only [h1110, h1557, hlam]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1108, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1513, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1521, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1523, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1109, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1514, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1109, h1111, hc23, hlam, hphi, p1529_1, u3elo3]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1109, h1111, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1529_1, u3elo3, u5ehi2]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1110, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1515, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h0, h1107, h1515, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1529_1]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [h1525, hlam, p1529_0]
                                    · have p1529_0 := h1529c.1
                                      have p1529_1 := h1529c.2.1
                                      have p1529_2 := h1529c.2.2.1
                                      have p1529_3 := h1529c.2.2.2
                                      linarith only [hlam, p1529_0]
                                  · linarith only [h1510, h1527, hlam, ht01, ht12, ht23, u3elo4]
                                  · linarith only [h1111, h1527, hlam, ht01, ht12, ht23, u3elo3]
                                  · linarith only [h0, h1107, h1527, hc12, hlam, ht01]
                                · linarith only [h1111, h1512, h1526, hlam]
                              · linarith only [h1111, h1512, h1521, h1525, hc23, hlam, hphi, u3elo3]
                        · linarith only [h1111, h1512, h1513, h1516, h1520, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1107, h1515, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1514, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1107, h1513, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1584 | h1584
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1585 | h1585
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1586 | h1586
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1587 | h1587
                    · linarith only [h1111, h1587, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1589 | h1589
                      · linarith only [h1587, h1589, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1591 | h1591
                        · linarith only [h1108, h1111, h1512, h1587, h1591, hc23, hlam, hphi, u3elo3]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1593 | h1593
                          · linarith only [h1108, h1111, h1593, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1595 | h1595
                            · linarith only [h0, h1107, h1510, h1584, h1587, h1591, h1595, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1597 | h1597
                              · linarith only [h1109, h1512, h1597, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1599 | h1599
                                · linarith only [h1108, h1111, h1512, h1599, hc23, hlam, hphi, u3elo3]
                                · rcases h0emin with h1601 | h1601 | h1601 | h1601 | h1601
                                  · linarith only [h0, h1601, hc12, hlam, ht01]
                                  · rcases h2bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h0, hlam, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1606 | h1606
                                      · rcases p1603_3 (m.d 1 2) (by simp) with h1607 | h1607
                                        · rcases p1603_3 (m.d 2 3) (by simp) with h1608 | h1608
                                          · linarith only [h1608, hlam, p1603_0]
                                          · rcases p1603_3 (m.d 2 4) (by simp) with h1610 | h1610
                                            · linarith only [h1109, h1610, hlam]
                                            · linarith only [h1593, h1610, hlam]
                                        · linarith only [h1584, h1607, hlam]
                                      · linarith only [h1606, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1615 | h1615
                                      · rcases p1603_3 (m.d 1 2) (by simp) with h1616 | h1616
                                        · rcases p1603_3 (m.d 2 3) (by simp) with h1617 | h1617
                                          · linarith only [h1108, h1617, hlam]
                                          · rcases p1603_3 (m.d 2 4) (by simp) with h1619 | h1619
                                            · linarith only [h1619, hlam, p1603_0]
                                            · rcases p1603_3 (m.d 2 5) (by simp) with h1621 | h1621
                                              · linarith only [h1110, h1621, hlam]
                                              · linarith only [h1597, h1621, hlam]
                                        · linarith only [h1585, h1616, hlam]
                                      · linarith only [h1615, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1626 | h1626
                                      · rcases p1603_3 (m.d 1 2) (by simp) with h1627 | h1627
                                        · rcases p1603_3 (m.d 2 3) (by simp) with h1628 | h1628
                                          · linarith only [h1108, h1628, hlam]
                                          · rcases p1603_3 (m.d 2 4) (by simp) with h1630 | h1630
                                            · linarith only [h1109, h1630, hlam]
                                            · rcases p1603_3 (m.d 2 5) (by simp) with h1632 | h1632
                                              · linarith only [h1632, hlam, p1603_0]
                                              · rcases h2emin with h1634 | h1634 | h1634 | h1634 | h1634
                                                · rcases h5bigk with h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c | h1635c
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, p1635_0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1510, h1586, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1635_1, u3elo4, u5ehi2]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1510, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1635_1, u3elo4, u5ehi2]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1510, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1512, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1107, hlam, p1635_0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, p1635_0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1635_1, u5ehi2]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1589, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1591, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1110, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1586, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, p1635_0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1595, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1597, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1635_1, u3elo4, u5ehi0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1586, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1635_1, u3elo4, u5ehi2]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1635_1, u3elo4, u5ehi2]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, p1635_0]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1599, hlam, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    rcases p1635_3 (m.d 0 5) (by simp) with h1656 | h1656
                                                    · linarith only [h1512, h1656, hlam]
                                                    · rcases p1635_3 (m.d 1 5) (by simp) with h1658 | h1658
                                                      · linarith only [h1591, h1658, hlam]
                                                      · rcases p1635_3 (m.d 2 5) (by simp) with h1660 | h1660
                                                        · linarith only [h1597, h1660, hlam]
                                                        · rcases p1635_3 (m.d 3 5) (by simp) with h1662 | h1662
                                                          · linarith only [h1599, h1662, hlam]
                                                          · linarith only [h1510, h1662, hlam]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    rcases p1635_3 (m.d 0 5) (by simp) with h1665 | h1665
                                                    · linarith only [h1512, h1665, hlam]
                                                    · linarith only [h1107, h1665, hlam]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    rcases p1635_3 (m.d 0 5) (by simp) with h1668 | h1668
                                                    · linarith only [h1512, h1668, hlam]
                                                    · linarith only [h1110, h1668, hlam]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [h1108, h1510, hc23, hc45, hlam, hphi, ht34, p1635_1]
                                                  · have p1635_0 := h1635c.1
                                                    have p1635_1 := h1635c.2.1
                                                    have p1635_2 := h1635c.2.2.1
                                                    have p1635_3 := h1635c.2.2.2
                                                    linarith only [hlam, p1635_0]
                                                · rcases h5bigk with h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c | h1673c
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, p1673_0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h0, h1107, h1586, hc12, hlam, hphi, ht01, ht0b, ht5b, p1673_1, u5ehi2]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1673_1, u5ehi2]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1510, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1512, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1107, hlam, p1673_0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, p1673_0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h0, h1107, hc12, hlam, hphi, ht01, ht0b, ht5b, p1673_1, u5ehi2]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1589, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1591, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1110, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1586, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, p1673_0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1595, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1597, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1673_1, u3elo4, u5ehi0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1673_1, u3elo4, u5ehi1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1673_1, u3elo4, u5ehi2]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, p1673_0]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1599, hlam, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    rcases p1673_3 (m.d 0 5) (by simp) with h1694 | h1694
                                                    · linarith only [h1512, h1694, hlam]
                                                    · rcases p1673_3 (m.d 1 5) (by simp) with h1696 | h1696
                                                      · linarith only [h1591, h1696, hlam]
                                                      · rcases p1673_3 (m.d 2 5) (by simp) with h1698 | h1698
                                                        · linarith only [h1597, h1698, hlam]
                                                        · rcases p1673_3 (m.d 3 5) (by simp) with h1700 | h1700
                                                          · linarith only [h1599, h1700, hlam]
                                                          · linarith only [h1510, h1700, hlam]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    rcases p1673_3 (m.d 0 5) (by simp) with h1703 | h1703
                                                    · linarith only [h1512, h1703, hlam]
                                                    · linarith only [h1107, h1703, hlam]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    rcases p1673_3 (m.d 0 5) (by simp) with h1706 | h1706
                                                    · linarith only [h1512, h1706, hlam]
                                                    · linarith only [h1110, h1706, hlam]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [h1108, h1510, hc23, hc45, hlam, hphi, ht34, p1673_1]
                                                  · have p1673_0 := h1673c.1
                                                    have p1673_1 := h1673c.2.1
                                                    have p1673_2 := h1673c.2.2.1
                                                    have p1673_3 := h1673c.2.2.2
                                                    linarith only [hlam, p1673_0]
                                                · linarith only [h1108, h1111, h1634, hlam, ht23, u3elo3]
                                                · linarith only [h1109, h1111, h1634, hlam, ht23, u3elo3]
                                                · linarith only [h0, h1107, h1586, h1634, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                        · linarith only [h1586, h1627, hlam]
                                      · linarith only [h1626, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1601, hc12, hlam, ht01, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1718 | h1718
                                      · linarith only [h0, h1718, hlam]
                                      · linarith only [h1108, h1718, hlam]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1721 | h1721
                                      · linarith only [h0, h1721, hlam]
                                      · linarith only [h1109, h1721, hlam]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      rcases p1603_3 (m.d 0 2) (by simp) with h1724 | h1724
                                      · linarith only [h0, h1724, hlam]
                                      · linarith only [h1110, h1724, hlam]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1108, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1584, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1593, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1595, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1109, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1585, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h0, h1107, h1585, h1591, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1597, hlam, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1110, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h1586, hlam, p1603_0]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h0, h1107, h1586, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [h0, h1107, h1586, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1603_1]
                                    · have p1603_0 := h1603c.1
                                      have p1603_1 := h1603c.2.1
                                      have p1603_2 := h1603c.2.2.1
                                      have p1603_3 := h1603c.2.2.2
                                      linarith only [hlam, p1603_0]
                                  · linarith only [h1111, h1599, h1601, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h1111, h1599, h1601, hc45, hlam, ht01, ht12, ht23, ht34]
                                  · linarith only [h0, h1107, h1601, hc12, hlam, ht01]
                  · linarith only [h0, h1107, h1586, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1585, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1107, h1584, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · linarith only [h0, h1107, h1110, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1749 | h1749
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1750 | h1750
        · linarith only [h1108, h1109, h1750, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1752 | h1752
          · linarith only [h1750, h1752, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1754 | h1754
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1756 | h1756
                · linarith only [h0, h1107, h1109, h1756, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                · linarith only [h0, h1107, h1756, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
              · linarith only [h0, h1107, h1108, h1755, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
            · linarith only [h0, h1107, h1109, h1754, hlam]
      · linarith only [h0, h1107, h1749, hlam]
  · linarith only [h0, h1107, h1108, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi1]

end R2N4
