import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1049 | h1049
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1050 | h1050
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1051 | h1051
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1052 | h1052
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1053 | h1053
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1054 | h1054
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1055 | h1055
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1057 | h1057
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1058 | h1058
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1059 | h1059
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1060 | h1060
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1061 | h1061
                          · linarith only [h1053, h1058, h1061, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h1052, h1061, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h1049, h1057, h1060, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1049, h1051, h1059, hc23, hlam, hphi, ht34, u4elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1066 | h1066
                      · linarith only [h1055, h1058, h1066, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
                      · linarith only [h0, h1049, h1051, h1066, hc23, hlam, hphi, ht34, u4elo1]
                  · linarith only [h0, h1049, h1054, h1057, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                · linarith only [h0, h1049, h1051, h1056, hc13, hlam, hphi, ht34, u4elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1072 | h1072
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1073 | h1073
                    · linarith only [h0, h1049, h1053, h1054, h1055, h1073, hc25, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1075 | h1075
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1076 | h1076
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1077 | h1077
                          · rcases h5bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1054, h1055, h1075, h1077, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1055, h1075, h1077, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1055, h1077, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1055, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1049, hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1075, h1077, hc45, hlam, hphi, ht01, ht0b, ht5b, p1078_1, u1elo4]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1055, h1077, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1055, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1050, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1054, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1050, h1077, hc02, hc45, hlam, hphi, ht0b, ht5b, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h0, h1049, h1054, h1055, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1078_1, u4elo3]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1051, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1071, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1075, hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [hlam, p1078_0]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1053, h1075, hc45, hlam, hphi, ht01, ht0b, ht5b, p1078_1, u1elo2]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1052, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1072, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1076, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [h1077, hlam, p1078_1]
                            · have p1078_0 := h1078c.1
                              have p1078_1 := h1078c.2.1
                              have p1078_2 := h1078c.2.2.1
                              have p1078_3 := h1078c.2.2.2
                              linarith only [hlam, p1078_0]
                          · linarith only [h0, h1055, h1077, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h1049, h1072, h1076, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                      · linarith only [h0, h1049, h1051, h1055, h1075, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h0, h1072, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1049, h1051, h1055, h1071, hc13, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h1049, h1050, h1054, hc12, hlam, hphi, ht23, ht34, u4elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1110 | h1110
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1111 | h1111
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1112 | h1112
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1113 | h1113
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1114 | h1114
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1115 | h1115
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1116 | h1116
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1117 | h1117
                          · rcases h5bigk with h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, h1115, h1117, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, h1117, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1049, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1115, h1117, hc45, hlam, hphi, ht01, ht0b, ht5b, p1118_1, u1elo4]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, h1117, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1050, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1110, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1110, h1117, hc45, hlam, hphi, ht01, ht0b, ht5b, p1118_1, u1elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h0, h1049, h1110, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1118_1, u4elo1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1112, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1115, hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1051, hc03, hc45, hlam, hphi, ht0b, ht5b, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1052, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1113, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1116, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [h1117, hlam, p1118_1]
                            · have p1118_0 := h1118c.1
                              have p1118_1 := h1118c.2.1
                              have p1118_2 := h1118c.2.2.1
                              have p1118_3 := h1118c.2.2.2
                              linarith only [hlam, p1118_0]
                          · linarith only [h0, h1052, h1117, hc34, hlam, hphi, u4elo1]
                        · linarith only [h0, h1049, h1113, h1114, h1116, hc34, hlam, hphi, u4elo1]
                      · linarith only [h0, h1049, h1051, h1053, h1111, h1115, hc03, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1053, h1114, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h1113, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1049, h1051, h1111, h1112, hc03, hc15, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1151 | h1151
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1153 | h1153
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1154 | h1154
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1155 | h1155
                          · rcases h5bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1110, h1111, h1152, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1111, h1152, h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1111, h1152, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1111, h1152, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1049, hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1153, h1155, hc45, hlam, hphi, ht01, ht0b, ht5b, p1156_1, u1elo4]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1111, h1152, h1155, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1111, h1152, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1050, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1110, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1110, h1155, hc45, hlam, hphi, ht01, ht0b, ht5b, p1156_1, u1elo1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h0, h1049, h1110, h1111, h1152, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1156_1, u4elo2]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1051, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1150, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1153, hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [hlam, p1156_0]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1051, hc03, hc45, hlam, hphi, ht0b, ht5b, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1052, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1151, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1154, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [h1155, hlam, p1156_1]
                            · have p1156_0 := h1156c.1
                              have p1156_1 := h1156c.2.1
                              have p1156_2 := h1156c.2.2.1
                              have p1156_3 := h1156c.2.2.2
                              linarith only [hlam, p1156_0]
                          · linarith only [h0, h1111, h1155, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h1049, h1111, h1151, h1152, h1154, hlam]
                      · linarith only [h0, h1049, h1110, h1111, h1152, h1153, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1053, h1152, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h1049, h1110, h1151, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                · linarith only [h0, h1049, h1051, h1150, hc13, hlam, hphi, ht34, u4elo1]
            · linarith only [h0, h1049, h1050, h1110, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · linarith only [h0, h1049, h1052, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1190 | h1190
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1192 | h1192
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1193 | h1193
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1194 | h1194
                · linarith only [h0, h1049, h1051, h1194, hc03, hlam, hphi, ht34, u4elo0]
                · linarith only [h0, h1049, h1194, hc13, hlam, hphi, ht34, u4elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1197 | h1197
                · linarith only [h1051, h1193, h1197, hc03, hlam, hphi, ht34, u4elo3]
                · linarith only [h0, h1049, h1193, h1197, hc13, hlam, hphi, ht34, u4elo3]
            · linarith only [h0, h1049, h1050, h1191, h1192, hc23, hlam, hphi, ht34, u4elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1201 | h1201
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1203 | h1203
                · linarith only [h0, h1049, h1051, h1203, hc03, hlam, hphi, ht34, u4elo1]
                · linarith only [h0, h1049, h1203, hc13, hlam, hphi, ht34, u4elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                · linarith only [h1051, h1202, h1206, hc03, hlam, hphi, ht34, u4elo3]
                · linarith only [h0, h1049, h1191, h1202, h1206, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · linarith only [h0, h1049, h1050, h1201, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · linarith only [h0, h1049, h1190, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1211 | h1211
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1212 | h1212
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1213 | h1213
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1214 | h1214
            · linarith only [h0, h1049, h1050, h1214, hc02, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h0, h1049, h1214, hc12, hlam, hphi, ht23, ht34, u4elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1217 | h1217
            · linarith only [h1050, h1213, h1217, hc02, hc23, hlam, hphi]
            · linarith only [h0, h1049, h1217, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · linarith only [h0, h1049, h1212, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1221 | h1221
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1222 | h1222
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1223 | h1223
            · linarith only [h0, h1049, h1050, h1223, hc02, hlam, hphi, ht23, ht34, u4elo0]
            · linarith only [h0, h1049, h1222, h1223, hc23, hlam, hphi, ht34, u4elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1226 | h1226
            · linarith only [h1050, h1222, h1226, hc02, hc23, hlam, hphi]
            · linarith only [h0, h1049, h1226, hc12, hlam, hphi, ht23, ht34, u4elo1]
        · linarith only [h0, h1049, h1221, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1230 | h1230
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1231 | h1231
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1232 | h1232
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1233 | h1233
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1234 | h1234
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1235 | h1235
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1236 | h1236
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1238 | h1238
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1239 | h1239
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1240 | h1240
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1241 | h1241
                          · linarith only [h1233, h1238, h1241, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h1232, h1241, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h1232, h1240, hc24, hlam, hphi, u4elo1]
                      · linarith only [h0, h1231, h1232, h1238, h1239, hc34, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1246 | h1246
                      · linarith only [h1233, h1235, h1238, h1246, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1248 | h1248
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1249 | h1249
                          · rcases h5bigk with h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [hlam, p1250_0]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1049, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h0, h1232, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1250_1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h0, h1232, h1246, hc23, hlam, hphi, ht34, p1250_1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h0, h1232, h1233, h1235, h1246, h1249, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1250_1, u1elo1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1233, h1235, h1237, h1246, h1249, hc05, hc23, hlam, hphi, ht01, ht0b, ht34, ht5b, p1250_1, u1elo1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [hlam, p1250_0]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1233, h1235, h1237, h1246, h1249, hc23, hc25, hlam, hphi, ht01, ht0b, ht34, ht5b, p1250_1, u1elo1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1237, h1246, hc23, hlam, hphi, ht34, p1250_1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1233, h1235, h1237, h1246, h1249, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1250_1, u1elo1, u4elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1230, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1234, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [hlam, p1250_0]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1246, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1230, hc02, hc45, hlam, hphi, ht0b, ht5b, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1231, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1236, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1233, h1235, h1249, hc25, hlam, hphi, ht01, ht0b, ht5b, p1250_1, u1elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [hlam, p1250_0]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1233, h1235, h1249, hc45, hlam, hphi, ht01, ht0b, ht5b, p1250_1, u1elo1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1232, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1237, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1248, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [h1249, hlam, p1250_1]
                            · have p1250_0 := h1250c.1
                              have p1250_1 := h1250c.2.1
                              have p1250_2 := h1250c.2.2.1
                              have p1250_3 := h1250c.2.2.2
                              linarith only [hlam, p1250_0]
                          · linarith only [h0, h1232, h1238, h1249, hc24, hlam, hphi, u4elo1]
                        · linarith only [h0, h1232, h1238, h1248, hc23, hlam, hphi, ht34, u4elo1]
                  · linarith only [h0, h1232, h1237, hlam]
                · linarith only [h0, h1231, h1232, h1235, h1236, hc34, hlam, hphi, u4elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1280 | h1280
                · linarith only [h1049, h1235, h1280, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1231, h1280, hlam]
            · linarith only [h1230, h1232, h1233, h1234, hc23, hlam, hphi, ht34, u4elo0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1284 | h1284
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1285 | h1285
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1286 | h1286
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1287 | h1287
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1288 | h1288
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1289 | h1289
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1290 | h1290
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1291 | h1291
                          · rcases h5bigk with h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1049, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h0, h1232, hc25, hlam, hphi, ht01, ht0b, ht5b, p1292_1, u1elo3]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h0, h1232, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1292_1, u4elo1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h0, h1232, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1292_1, u4elo1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1292_1, u1elo4]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1284, h1289, hc35, hlam, hphi, ht01, ht0b, ht5b, p1292_1, u1elo1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1233, h1284, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1287, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1292_1, u4elo1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1230, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1284, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1230, hc02, hc35, hlam, hphi, ht0b, ht5b, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1233, h1284, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1231, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1286, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1289, hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1231, hc03, hc45, hlam, hphi, ht0b, ht5b, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1232, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1287, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1290, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [h1291, hlam, p1292_1]
                            · have p1292_0 := h1292c.1
                              have p1292_1 := h1292c.2.1
                              have p1292_2 := h1292c.2.2.1
                              have p1292_3 := h1292c.2.2.2
                              linarith only [hlam, p1292_0]
                          · linarith only [h0, h1232, h1291, hc34, hlam, hphi, u4elo1]
                        · linarith only [h0, h1232, h1290, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1231, h1233, h1284, h1289, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1233, h1288, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h1287, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1231, h1232, h1285, h1286, hc34, hlam, hphi, u4elo0]
              · linarith only [h1049, h1233, h1284, h1285, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1049, h1230, h1284, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1326 | h1326
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1327 | h1327
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1328 | h1328
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1329 | h1329
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1330 | h1330
                  · linarith only [h1232, h1330, hc04, hlam, hphi, u4elo1]
                  · linarith only [h0, h1330, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1049, h1231, h1328, h1329, hc01, hlam, hphi, u1elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1334 | h1334
                · linarith only [h1049, h1328, h1334, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1231, h1334, hlam]
            · linarith only [h1230, h1232, h1326, h1327, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1338 | h1338
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1339 | h1339
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1341 | h1341
                  · linarith only [h0, h1232, h1341, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                  · linarith only [h0, h1341, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1049, h1231, h1326, h1338, h1340, hlam]
              · linarith only [h1049, h1326, h1338, h1339, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1049, h1230, h1338, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1347 | h1347
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1348 | h1348
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1349 | h1349
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1350 | h1350
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1351 | h1351
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1352 | h1352
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1353 | h1353
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1354 | h1354
                      · linarith only [h1231, h1348, h1354, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h1348, h1351, h1353, h1354, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1357 | h1357
                      · linarith only [h1231, h1353, h1357, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1359 | h1359
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1360 | h1360
                          · rcases h5bigk with h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hlam, p1361_0]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1049, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1231, h1348, h1350, h1360, hc25, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1231, hlam, p1361_0]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1231, h1348, h1350, h1360, hc45, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo4]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hlam, p1361_0]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1349, hc25, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1231, h1348, h1351, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1352, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1361_1, u4elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1230, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1349, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hlam, p1361_0]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1357, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1230, hc02, hc45, hlam, hphi, ht0b, ht5b, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1049, hc01, hc35, hlam, hphi, ht12, ht23, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1351, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1348, h1351, hc25, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hlam, p1361_0]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1348, h1350, h1360, hc45, hlam, hphi, ht01, ht0b, ht5b, p1361_1, u1elo1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1347, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1352, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1359, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [h1360, hlam, p1361_1]
                            · have p1361_0 := h1361c.1
                              have p1361_1 := h1361c.2.1
                              have p1361_2 := h1361c.2.2.1
                              have p1361_3 := h1361c.2.2.2
                              linarith only [hlam, p1361_0]
                          · linarith only [h1359, h1360, hc34, hlam, hphi, u4elo2]
                        · linarith only [h0, h1347, h1359, hc24, hlam, hphi, u4elo1]
                  · linarith only [h0, h1347, h1352, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1390 | h1390
                  · linarith only [h1350, h1351, h1390, hlam]
                  · linarith only [h0, h1347, h1390, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1393 | h1393
                · linarith only [h1231, h1350, h1393, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1395 | h1395
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1396 | h1396
                    · linarith only [h1348, h1350, h1396, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1398 | h1398
                      · linarith only [h1348, h1393, h1398, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1400 | h1400
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1401 | h1401
                          · rcases h5bigk with h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1049, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, h1347, h1398, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1402_1, u1elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1231, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h0, h1347, h1350, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1350, h1395, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1350, h1395, h1398, hc23, hlam, hphi, ht34, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1393, hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1350, h1395, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1230, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1349, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1398, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1230, hc02, hc45, hlam, hphi, ht0b, ht5b, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1401, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1401, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1401, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1401, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1402_1, u4elo3]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1347, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1395, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1400, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [h1401, hlam, p1402_1]
                            · have p1402_0 := h1402c.1
                              have p1402_1 := h1402c.2.1
                              have p1402_2 := h1402c.2.2.1
                              have p1402_3 := h1402c.2.2.2
                              linarith only [hlam, p1402_0]
                          · linarith only [h0, h1350, h1400, h1401, hc04, hlam, hphi, u4elo2]
                        · linarith only [h1347, h1400, hc24, hlam, hphi, u4elo0]
                  · linarith only [h0, h1395, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · linarith only [h0, h1230, h1347, h1348, h1349, hc23, hlam, hphi, ht34, u4elo1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1432 | h1432
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1433 | h1433
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1434 | h1434
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1435 | h1435
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1436 | h1436
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1437 | h1437
                      · linarith only [h1230, h1231, h1437, hlam]
                      · linarith only [h1049, h1348, h1432, h1437, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1049, h1348, h1432, h1433, h1436, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h1435, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1348, h1432, h1434, hlam]
              · linarith only [h1049, h1348, h1432, h1433, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1049, h1230, h1432, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                  · linarith only [h1347, h1449, hc04, hlam, hphi, u4elo1]
                  · linarith only [h0, h1449, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1452 | h1452
                  · linarith only [h0, h1347, h1447, h1448, h1452, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h1452, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1455 | h1455
                · linarith only [h1231, h1447, h1455, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1457 | h1457
                  · linarith only [h0, h1347, h1457, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1457, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · linarith only [h1230, h1347, h1445, h1446, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1461 | h1461
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1462 | h1462
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1463 | h1463
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1464 | h1464
                  · linarith only [h0, h1347, h1464, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1464, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1445, h1461, h1463, hlam]
              · linarith only [h1049, h1445, h1461, h1462, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h1049, h1230, h1461, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1470 | h1470
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1471 | h1471
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1472 | h1472
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1473 | h1473
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1474 | h1474
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1475 | h1475
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1477 | h1477
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1478 | h1478
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1479 | h1479
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1480 | h1480
                          · linarith only [h1472, h1477, h1480, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                          · linarith only [h1471, h1480, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h1471, h1479, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1049, h1470, h1476, h1477, h1478, hc34, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1485 | h1485
                      · linarith only [h1472, h1474, h1477, h1485, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h1230, h1470, h1485, hlam]
                  · linarith only [h0, h1471, h1476, hlam]
                · linarith only [h1230, h1470, h1473, h1474, h1475, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1490 | h1490
                · linarith only [h1049, h1474, h1490, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1230, h1470, h1473, h1490, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1493 | h1493
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1494 | h1494
                · linarith only [h1472, h1473, h1494, hlam]
                · linarith only [h0, h1470, h1471, h1493, h1494, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                · linarith only [h1049, h1493, h1497, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1470, h1497, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1500 | h1500
            · linarith only [h1230, h1472, h1500, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1502 | h1502
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1503 | h1503
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1505 | h1505
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1506 | h1506
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1507 | h1507
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1508 | h1508
                          · rcases h5bigk with h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1049, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1230, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1049, h1500, h1507, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1049, h1500, h1507, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1500, h1507, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1500, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1500, h1507, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1500, h1507, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1049, h1507, hc01, hlam, hphi, ht12, ht23, ht34, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1507, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1507, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1507, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1509_1, u4elo2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1470, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1503, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1506, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1470, hc03, hc45, hlam, hphi, ht0b, ht5b, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1471, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1504, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1507, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1508, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                          · linarith only [h0, h1471, h1508, hc34, hlam, hphi, u4elo1]
                        · linarith only [h0, h1471, h1507, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1472, h1503, h1506, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                    · linarith only [h1472, h1505, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h1471, h1504, hlam]
                · linarith only [h0, h1049, h1470, h1502, h1503, hc01, hlam, hphi, u1elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1541 | h1541
                · linarith only [h1049, h1502, h1541, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1470, h1541, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1544 | h1544
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1545 | h1545
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1546 | h1546
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1547 | h1547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1548 | h1548
                  · linarith only [h1471, h1548, hc04, hlam, hphi, u4elo1]
                  · linarith only [h0, h1548, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h0, h1230, h1470, h1545, h1546, h1547, hc01, hlam, hphi, u1elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1552 | h1552
                · linarith only [h1049, h1546, h1552, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1230, h1470, h1545, h1552, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1555 | h1555
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1556 | h1556
                · linarith only [h1544, h1545, h1556, hlam]
                · linarith only [h0, h1049, h1470, h1555, h1556, hc01, hlam, hphi, u1elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1559 | h1559
                · linarith only [h1049, h1555, h1559, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1470, h1559, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1562 | h1562
            · linarith only [h1230, h1544, h1562, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1564 | h1564
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1565 | h1565
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1566 | h1566
                  · linarith only [h0, h1471, h1566, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                  · linarith only [h0, h1566, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h1470, h1471, h1564, h1565, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1570 | h1570
                · linarith only [h1049, h1564, h1570, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h1049, h1470, h1570, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1573 | h1573
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1574 | h1574
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1575 | h1575
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1576 | h1576
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1577 | h1577
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1578 | h1578
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1579 | h1579
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1580 | h1580
                      · linarith only [h1470, h1574, h1580, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                      · linarith only [h1577, h1579, h1580, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                      · linarith only [h1049, h1470, h1579, h1583, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1585 | h1585
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1586 | h1586
                          · rcases h5bigk with h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c | h1587c
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1049, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1470, hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1049, h1230, h1574, h1576, h1578, h1579, h1585, hc02, hc45, hlam, hphi, ht01, ht0b, ht23, ht34, ht5b, p1587_1, u1elo1, u4elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, h1574, h1576, h1578, h1579, h1585, hc02, hc05, hlam, hphi, ht01, ht0b, ht23, ht34, ht5b, p1587_1, u1elo1, u4elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, h1578, hc02, hlam, hphi, ht23, ht34, p1587_1, u4elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, h1578, h1583, hc02, hlam, hphi, ht23, ht34, p1587_1, u4elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, h1574, h1576, h1578, h1579, h1585, hc02, hc45, hlam, hphi, ht01, ht0b, ht23, ht34, ht5b, p1587_1, u1elo1, u4elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1049, h1574, h1576, h1579, h1585, hc01, hlam, hphi, p1587_1, u1elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1575, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1583, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1574, h1576, h1579, h1585, hc45, hlam, hphi, ht01, ht0b, ht5b, p1587_1, u1elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1049, h1230, h1574, h1576, h1579, h1585, hc01, hc02, hc35, hlam, hphi, ht23, p1587_1, u1elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1577, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1230, h1574, h1577, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1587_1, u1elo1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [hlam, p1587_0]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1586, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1587_1, u4elo3]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1573, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1578, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1585, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [h1586, hlam, p1587_1]
                            · have p1587_0 := h1587c.1
                              have p1587_1 := h1587c.2.1
                              have p1587_2 := h1587c.2.2.1
                              have p1587_3 := h1587c.2.2.2
                              linarith only [hlam, p1587_0]
                          · linarith only [h1230, h1579, h1585, h1586, hc02, hlam, hphi, ht23, ht34, u4elo4]
                        · linarith only [h0, h1573, h1585, hc24, hlam, hphi, u4elo1]
                  · linarith only [h0, h1573, h1578, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1616 | h1616
                  · linarith only [h1576, h1577, h1616, hlam]
                  · linarith only [h0, h1573, h1616, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1619 | h1619
                · linarith only [h1470, h1576, h1619, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1621 | h1621
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1622 | h1622
                    · linarith only [h1574, h1576, h1622, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1624 | h1624
                      · linarith only [h1574, h1619, h1624, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1626 | h1626
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1627 | h1627
                          · rcases h5bigk with h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1049, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1230, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1470, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1049, h1621, hc45, hlam, hphi, ht01, ht0b, ht5b, p1628_1, u1elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1621, hc05, hlam, hphi, ht01, ht0b, ht5b, p1628_1, u1elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1230, h1576, h1621, hc02, hlam, hphi, ht23, ht34, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1619, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1576, h1621, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1049, hc01, hc25, hlam, hphi, ht12, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1575, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1624, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1575, hc45, hlam, hphi, ht01, ht0b, ht5b, p1628_1, u1elo1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1049, h1627, hc01, hlam, hphi, ht12, ht23, ht34, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1627, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1627, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1627, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1628_1, u4elo3]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1573, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1621, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1626, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1627, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                          · linarith only [h0, h1576, h1627, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1573, h1626, hc24, hlam, hphi, u4elo0]
                  · linarith only [h0, h1573, h1621, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1657 | h1657
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1658 | h1658
                · linarith only [h1574, h1575, h1658, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1660 | h1660
                  · linarith only [h1574, h1575, h1657, h1660, hlam]
                  · linarith only [h1573, h1660, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1663 | h1663
                · linarith only [h1470, h1657, h1663, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1666 | h1666
                    · linarith only [h1574, h1575, h1657, h1665, h1666, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1668 | h1668
                      · linarith only [h1574, h1575, h1657, h1663, h1665, h1668, hc13, hlam, hphi, ht34, u4elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1670 | h1670
                        · linarith only [h1574, h1575, h1670, hc23, hlam, hphi, ht34, u4elo2]
                        · linarith only [h0, h1573, h1657, h1670, hc24, hlam, hphi, u4elo3]
                  · linarith only [h0, h1573, h1665, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1674 | h1674
            · linarith only [h1230, h1574, h1674, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1676 | h1676
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1678 | h1678
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1680 | h1680
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1681 | h1681
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1682 | h1682
                          · rcases h5bigk with h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c | h1683c
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1049, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1230, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1470, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1049, h1678, hc45, hlam, hphi, ht01, ht0b, ht5b, p1683_1, u1elo3]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1678, hc05, hlam, hphi, ht01, ht0b, ht5b, p1683_1, u1elo3]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1674, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1470, h1674, h1681, hc03, hlam, hphi, ht34, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1674, h1681, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1049, h1681, hc01, hlam, hphi, ht12, ht23, ht34, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1681, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1470, h1681, hc03, hlam, hphi, ht34, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1681, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1683_1, u4elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1049, hc01, hc35, hlam, hphi, ht12, ht23, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1677, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1680, hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1676, h1682, hc45, hlam, hphi, ht01, ht0b, ht5b, p1683_1, u1elo2]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1573, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1678, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1681, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [h1682, hlam, p1683_1]
                            · have p1683_0 := h1683c.1
                              have p1683_1 := h1683c.2.1
                              have p1683_2 := h1683c.2.2.1
                              have p1683_3 := h1683c.2.2.2
                              linarith only [hlam, p1683_0]
                          · linarith only [h1573, h1682, hc34, hlam, hphi, u4elo0]
                        · linarith only [h0, h1573, h1681, hc24, hlam, hphi, u4elo1]
                      · linarith only [h1574, h1677, h1680, hlam]
                    · linarith only [h1470, h1574, h1677, h1679, hc03, hc34, hlam, hphi]
                  · linarith only [h0, h1573, h1678, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1714 | h1714
                  · linarith only [h1676, h1677, h1714, hlam]
                  · linarith only [h0, h1714, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1717 | h1717
                · linarith only [h1470, h1676, h1717, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1719 | h1719
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1720 | h1720
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1721 | h1721
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1722 | h1722
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1723 | h1723
                          · rcases h5bigk with h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1049, hlam, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1230, hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1470, hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1049, h1676, h1719, h1720, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1676, h1719, h1720, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1674, hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1717, hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1676, h1719, h1720, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1049, h1722, hc01, hlam, hphi, ht12, ht23, ht34, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1722, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1574, h1717, h1722, hc12, hlam, hphi, ht23, ht34, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1049, hc01, hc35, hlam, hphi, ht12, ht23, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1049, hc01, hc35, hlam, hphi, ht12, ht23, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1721, hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [hlam, p1724_0]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1721, h1722, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1724_1, u4elo2]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1573, hlam, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1719, hlam, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1722, hlam, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [h1723, hlam, p1724_1]
                            · have p1724_0 := h1724c.1
                              have p1724_1 := h1724c.2.1
                              have p1724_2 := h1724c.2.2.1
                              have p1724_3 := h1724c.2.2.2
                              linarith only [hlam, p1724_0]
                          · linarith only [h0, h1676, h1723, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h1573, h1722, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1049, h1676, h1719, h1720, h1721, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h1574, h1720, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h0, h1573, h1719, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1755 | h1755
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1756 | h1756
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1757 | h1757
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1758 | h1758
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1759 | h1759
                  · linarith only [h0, h1573, h1759, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1759, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1762 | h1762
                  · linarith only [h0, h1573, h1757, h1762, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h1762, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1765 | h1765
                · linarith only [h1470, h1757, h1765, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1767 | h1767
                  · linarith only [h0, h1573, h1767, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1767, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1770 | h1770
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1771 | h1771
                · linarith only [h1755, h1756, h1771, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1773 | h1773
                  · linarith only [h0, h1573, h1773, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1773, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1776 | h1776
                · linarith only [h1470, h1770, h1776, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1778 | h1778
                  · linarith only [h0, h1573, h1778, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1778, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1781 | h1781
            · linarith only [h1230, h1755, h1781, hc02, hc23, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1783 | h1783
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1784 | h1784
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1785 | h1785
                  · linarith only [h0, h1573, h1785, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1785, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1788 | h1788
                  · linarith only [h0, h1573, h1783, h1788, hc01, hlam, hphi, u1elo2]
                  · linarith only [h0, h1788, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1791 | h1791
                · linarith only [h1470, h1783, h1791, hc03, hlam, hphi, ht34, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1793 | h1793
                  · linarith only [h0, h1573, h1793, hc01, hlam, hphi, u1elo3]
                  · linarith only [h0, h1793, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]

set_option maxHeartbeats 3592000 in
set_option maxHeartbeats 3592000 in
theorem r1l7_11_12_14_25_L_0_L_I_L_0_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h4elo := hb4.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_0_L_I_L_0_H_I_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
