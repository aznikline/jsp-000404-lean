import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1028 | h1028
    · linarith only [h1028, h11, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1030 | h1030
      · linarith only [h10, h1030, h11, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1032 | h1032
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1033 | h1033
          · linarith only [h0, h1028, h1030, h1033, h11, h4, h6, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h1032, h1033, h11, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1027, h1028, h1032, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1037 | h1037
    · linarith only [h1037, h11, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1039 | h1039
      · linarith only [h10, h1039, h11, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1041 | h1041
        · linarith only [h0, h1027, h1041, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1043 | h1043
          · linarith only [h1037, h1043, h9, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1045 | h1045
            · linarith only [h0, h10, h1039, h1043, h1045, h11, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1047 | h1047
              · linarith only [h0, h10, h1045, h1047, h11, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c | h1049c
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  rcases p1049_3 (m.d 0 1) (by simp) with h1051 | h1051
                  · rcases p1049_3 (m.d 1 2) (by simp) with h1052 | h1052
                    · linarith only [h1052, hlam, p1049_0]
                    · rcases p1049_3 (m.d 1 3) (by simp) with h1054 | h1054
                      · linarith only [h1, h1054, hlam]
                      · rcases p1049_3 (m.d 1 4) (by simp) with h1056 | h1056
                        · linarith only [h1056, h2, hlam]
                        · rcases p1049_3 (m.d 1 5) (by simp) with h1058 | h1058
                          · linarith only [h1058, h3, hlam]
                          · linarith only [h1058, h11, hlam]
                  · linarith only [h1051, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, h1027, h1047, h4, h6, h8, hlam, p1049_2]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  rcases p1049_3 (m.d 0 1) (by simp) with h1063 | h1063
                  · rcases p1049_3 (m.d 1 2) (by simp) with h1064 | h1064
                    · linarith only [h0, h1064, hlam]
                    · linarith only [h10, h1064, hlam]
                  · linarith only [h1063, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  rcases p1049_3 (m.d 0 1) (by simp) with h1068 | h1068
                  · rcases p1049_3 (m.d 1 2) (by simp) with h1069 | h1069
                    · linarith only [h0, h1069, hlam]
                    · rcases p1049_3 (m.d 1 3) (by simp) with h1071 | h1071
                      · linarith only [h1, h1071, hlam]
                      · rcases p1049_3 (m.d 1 4) (by simp) with h1073 | h1073
                        · linarith only [h1073, h2, hlam]
                        · rcases p1049_3 (m.d 1 5) (by simp) with h1075 | h1075
                          · linarith only [h1075, hlam, p1049_0]
                          · rcases h3bigk with h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              rcases p1077_3 (m.d 0 3) (by simp) with h1079 | h1079
                              · rcases p1077_3 (m.d 1 3) (by simp) with h1080 | h1080
                                · linarith only [h1, h1080, hlam]
                                · rcases p1077_3 (m.d 2 3) (by simp) with h1082 | h1082
                                  · linarith only [h1082, h4, hlam]
                                  · rcases p1077_3 (m.d 3 4) (by simp) with h1084 | h1084
                                    · linarith only [h1084, h6, hlam]
                                    · linarith only [h1027, h1084, hlam]
                              · linarith only [h1, h1079, hlam]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              rcases p1077_3 (m.d 0 3) (by simp) with h1088 | h1088
                              · rcases p1077_3 (m.d 1 3) (by simp) with h1089 | h1089
                                · linarith only [h1, h1089, hlam]
                                · linarith only [h1089, h9, hlam]
                              · linarith only [h1088, h4, hlam]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h0, h1027, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h0, h1037, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1027, hc23, hc34, hlam, hphi, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1027, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1037, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h4, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h9, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1041, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1043, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h6, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hc13, hc34, hlam, hphi, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h1047, hlam, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h7, hlam, p1077_0]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h9, hc23, hc35, hlam, hphi, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [h0, h1047, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                            · have p1077_0 := h1077c.1
                              have p1077_1 := h1077c.2.1
                              have p1077_2 := h1077c.2.2.1
                              have p1077_3 := h1077c.2.2.2
                              linarith only [hlam, p1077_0]
                  · linarith only [h1068, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, h1043, h1047, h11, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, h10, h1041, h1043, h1047, h11, h4, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h11, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h1, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h9, hlam, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h1027, hlam, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h1037, hlam, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h2, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h10, hlam, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, h1039, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h1039, hlam, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h3, hlam, p1049_0]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [h0, h1037, h1047, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1049_1]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  rcases p1049_3 (m.d 0 1) (by simp) with h1133 | h1133
                  · rcases p1049_3 (m.d 1 2) (by simp) with h1134 | h1134
                    · linarith only [h11, h1134, hlam]
                    · linarith only [h1134, h9, hlam]
                  · linarith only [h1, h1133, hlam]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  rcases p1049_3 (m.d 0 1) (by simp) with h1138 | h1138
                  · rcases p1049_3 (m.d 1 2) (by simp) with h1139 | h1139
                    · linarith only [h11, h1139, hlam]
                    · linarith only [h10, h1139, hlam]
                  · linarith only [h1138, h2, hlam]
                · have p1049_0 := h1049c.1
                  have p1049_1 := h1049c.2.1
                  have p1049_2 := h1049c.2.2.1
                  have p1049_3 := h1049c.2.2.2
                  linarith only [hlam, p1049_0]

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
  · exact r1l7_11_23_L_I_H_I_s8_x0_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11
  · exact r1l7_11_23_L_I_H_I_s8_x0_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1145 | h1145
    · linarith only [h10, h1145, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1147 | h1147
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1148 | h1148
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1149 | h1149
          · linarith only [h0, h1145, h1147, h1149, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
            · linarith only [h0, h10, h1151, h5, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10, h1147, h1149, h1151, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h10, h1147, h1148, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1155 | h1155
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1156 | h1156
          · linarith only [h0, h10, h1156, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1158 | h1158
            · linarith only [h0, h10, h1147, h1156, h1158, h4, h6, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1160 | h1160
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1161 | h1161
                · rcases h1bigk with h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c | h1162c
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1164 | h1164
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1165 | h1165
                      · linarith only [h1165, hlam, p1162_0]
                      · rcases p1162_3 (m.d 1 3) (by simp) with h1167 | h1167
                        · linarith only [h1, h1167, hlam]
                        · rcases p1162_3 (m.d 1 4) (by simp) with h1169 | h1169
                          · linarith only [h1169, h2, hlam]
                          · linarith only [h10, h1169, hlam]
                    · linarith only [h1164, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1173 | h1173
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1174 | h1174
                      · linarith only [h0, h1174, hlam]
                      · linarith only [h1174, h9, hlam]
                    · linarith only [h1173, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1178 | h1178
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1179 | h1179
                      · linarith only [h0, h1179, hlam]
                      · rcases p1162_3 (m.d 1 3) (by simp) with h1181 | h1181
                        · linarith only [h1, h1181, hlam]
                        · rcases p1162_3 (m.d 1 4) (by simp) with h1183 | h1183
                          · linarith only [h1183, hlam, p1162_0]
                          · rcases p1162_3 (m.d 1 5) (by simp) with h1185 | h1185
                            · linarith only [h1185, h3, hlam]
                            · rcases h3bigk with h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                rcases p1187_3 (m.d 0 3) (by simp) with h1189 | h1189
                                · rcases p1187_3 (m.d 1 3) (by simp) with h1190 | h1190
                                  · linarith only [h1, h1190, hlam]
                                  · rcases p1187_3 (m.d 2 3) (by simp) with h1192 | h1192
                                    · linarith only [h1192, h4, hlam]
                                    · rcases p1187_3 (m.d 3 4) (by simp) with h1194 | h1194
                                      · linarith only [h1194, h6, hlam]
                                      · linarith only [h1145, h1194, hlam]
                                · linarith only [h1, h1189, hlam]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                rcases p1187_3 (m.d 0 3) (by simp) with h1198 | h1198
                                · rcases p1187_3 (m.d 1 3) (by simp) with h1199 | h1199
                                  · linarith only [h1, h1199, hlam]
                                  · linarith only [h1199, h9, hlam]
                                · linarith only [h1198, h4, hlam]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h0, h10, h1156, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h0, h1147, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1147, hc23, hc35, hlam, hphi, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1145, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1147, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h4, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h9, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1156, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1158, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h6, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hc13, hc34, hlam, hphi, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h0, h4, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h7, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h9, hc23, hc35, hlam, hphi, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1187_1]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [h1161, hlam, p1187_0]
                              · have p1187_0 := h1187c.1
                                have p1187_1 := h1187c.2.1
                                have p1187_2 := h1187c.2.2.1
                                have p1187_3 := h1187c.2.2.2
                                linarith only [hlam, p1187_0]
                    · linarith only [h1178, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1226 | h1226
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1227 | h1227
                      · linarith only [h0, h1227, hlam]
                      · linarith only [h1144, h1227, hlam]
                    · linarith only [h1226, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h0, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h0, h10, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h10, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h0, h10, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h1, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h9, hlam, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h1145, hlam, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h1147, hlam, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h2, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1243 | h1243
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1244 | h1244
                      · linarith only [h10, h1244, hlam]
                      · linarith only [h1244, h9, hlam]
                    · linarith only [h1, h1243, hlam]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    rcases p1162_3 (m.d 0 1) (by simp) with h1249 | h1249
                    · rcases p1162_3 (m.d 1 2) (by simp) with h1250 | h1250
                      · linarith only [h10, h1250, hlam]
                      · linarith only [h1144, h1250, hlam]
                    · linarith only [h1249, h3, hlam]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h3, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h1144, hlam, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h0, h10, h1144, h1156, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1162_1]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [h1155, hlam, p1162_0]
                  · have p1162_0 := h1162c.1
                    have p1162_1 := h1162c.2.1
                    have p1162_2 := h1162c.2.2.1
                    have p1162_3 := h1162c.2.2.2
                    linarith only [hlam, p1162_0]
                · linarith only [h0, h10, h1156, h1161, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h1144, h1155, h1160, hlam]
        · linarith only [h10, h1144, h1155, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1262 | h1262
    · linarith only [h10, h1262, h9, hlam]
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1264 | h1264
      · linarith only [h1144, h1264, h9, hlam]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1266 | h1266
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1267 | h1267
          · linarith only [h1144, h1262, h1267, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1269 | h1269
            · linarith only [h1144, h1264, h1269, h9, hlam]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1271 | h1271
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1272 | h1272
                · rcases h1bigk with h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c | h1273c
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1275 | h1275
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1276 | h1276
                      · linarith only [h1276, hlam, p1273_0]
                      · rcases p1273_3 (m.d 1 3) (by simp) with h1278 | h1278
                        · linarith only [h1, h1278, hlam]
                        · rcases p1273_3 (m.d 1 4) (by simp) with h1280 | h1280
                          · linarith only [h1280, h2, hlam]
                          · linarith only [h10, h1280, hlam]
                    · linarith only [h1275, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1284 | h1284
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1285 | h1285
                      · linarith only [h0, h1285, hlam]
                      · linarith only [h1285, h9, hlam]
                    · linarith only [h1284, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1289 | h1289
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1290 | h1290
                      · linarith only [h0, h1290, hlam]
                      · rcases p1273_3 (m.d 1 3) (by simp) with h1292 | h1292
                        · linarith only [h1, h1292, hlam]
                        · rcases p1273_3 (m.d 1 4) (by simp) with h1294 | h1294
                          · linarith only [h1294, hlam, p1273_0]
                          · rcases p1273_3 (m.d 1 5) (by simp) with h1296 | h1296
                            · linarith only [h1296, h3, hlam]
                            · rcases h3bigk with h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c | h1298c
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                rcases p1298_3 (m.d 0 3) (by simp) with h1300 | h1300
                                · rcases p1298_3 (m.d 1 3) (by simp) with h1301 | h1301
                                  · linarith only [h1, h1301, hlam]
                                  · rcases p1298_3 (m.d 2 3) (by simp) with h1303 | h1303
                                    · linarith only [h1303, h4, hlam]
                                    · rcases p1298_3 (m.d 3 4) (by simp) with h1305 | h1305
                                      · linarith only [h1305, h6, hlam]
                                      · linarith only [h1262, h1305, hlam]
                                · linarith only [h1, h1300, hlam]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                rcases p1298_3 (m.d 0 3) (by simp) with h1309 | h1309
                                · rcases p1298_3 (m.d 1 3) (by simp) with h1310 | h1310
                                  · linarith only [h1, h1310, hlam]
                                  · linarith only [h1310, h9, hlam]
                                · linarith only [h1309, h4, hlam]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h0, h1144, h1267, h1271, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h0, h1144, h1269, h4, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1262, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1264, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h4, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h9, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1267, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1269, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h6, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hc13, hc34, hlam, hphi, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h0, h1144, h1269, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h7, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h9, hc23, hc35, hlam, hphi, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h0, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1298_1]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [h1272, hlam, p1298_0]
                              · have p1298_0 := h1298c.1
                                have p1298_1 := h1298c.2.1
                                have p1298_2 := h1298c.2.2.1
                                have p1298_3 := h1298c.2.2.2
                                linarith only [hlam, p1298_0]
                    · linarith only [h1289, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1337 | h1337
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1338 | h1338
                      · linarith only [h0, h1338, hlam]
                      · rcases p1273_3 (m.d 1 3) (by simp) with h1340 | h1340
                        · linarith only [h1, h1340, hlam]
                        · rcases p1273_3 (m.d 1 4) (by simp) with h1342 | h1342
                          · linarith only [h1342, h2, hlam]
                          · linarith only [h1266, h1342, hlam]
                    · linarith only [h1337, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h0, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h0, h1144, h1271, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h10, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h1144, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h1, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h9, hlam, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h1262, hlam, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h1264, hlam, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h2, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h2, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1358 | h1358
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1359 | h1359
                      · linarith only [h10, h1359, hlam]
                      · linarith only [h1359, h9, hlam]
                    · linarith only [h1, h1358, hlam]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h0, h10, h1144, h1267, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h3, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h3, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1273_1]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    rcases p1273_3 (m.d 0 1) (by simp) with h1367 | h1367
                    · rcases p1273_3 (m.d 1 2) (by simp) with h1368 | h1368
                      · linarith only [h1144, h1368, hlam]
                      · linarith only [h1368, h9, hlam]
                    · linarith only [h1, h1367, hlam]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [h1266, hlam, p1273_0]
                  · have p1273_0 := h1273c.1
                    have p1273_1 := h1273c.2.1
                    have p1273_2 := h1273c.2.2.1
                    have p1273_3 := h1273c.2.2.2
                    linarith only [hlam, p1273_0]
                · linarith only [h10, h1266, h1267, h1272, hlam]
              · linarith only [h10, h1266, h1271, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1376 | h1376
          · linarith only [h0, h10, h1376, h5, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1378 | h1378
            · linarith only [h0, h10, h1266, h1378, h4, h6, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1380 | h1380
              · linarith only [h0, h10, h1266, h1376, h1380, h4, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h10, h1380, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
  · exact r1l7_11_23_L_I_H_I_s8_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10
  · exact r1l7_11_23_L_I_H_I_s8_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1383 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h1384 | h1384
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1385 | h1385
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1386 | h1386
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1387 | h1387
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1388 | h1388
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1389 | h1389
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1390 | h1390
              · linarith only [h0, h1383, h1390, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1383, h1387, h1390, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1384, h1389, h4, h7, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1384, h1388, h6, h9, hc03, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1395 | h1395
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1396 | h1396
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1397 | h1397
              · linarith only [h1383, h1387, h1397, h9, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1399 | h1399
                · linarith only [h0, h1383, h1387, h1395, h1399, h4, h9, hc01, hc15, hlam, hphi, ht0b, ht5b]
                · rcases h1bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1403 | h1403
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1404 | h1404
                      · linarith only [h1404, hlam, p1401_0]
                      · rcases p1401_3 (m.d 1 3) (by simp) with h1406 | h1406
                        · linarith only [h1, h1406, hlam]
                        · linarith only [h1406, h9, hlam]
                    · linarith only [h1403, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1410 | h1410
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1411 | h1411
                      · linarith only [h0, h1411, hlam]
                      · rcases p1401_3 (m.d 1 3) (by simp) with h1413 | h1413
                        · linarith only [h1413, hlam, p1401_0]
                        · rcases p1401_3 (m.d 1 4) (by simp) with h1415 | h1415
                          · linarith only [h1415, h2, hlam]
                          · rcases p1401_3 (m.d 1 5) (by simp) with h1417 | h1417
                            · linarith only [h1417, h3, hlam]
                            · rcases h3bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1384, h1397, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1384, h1395, h1397, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                rcases p1419_3 (m.d 0 3) (by simp) with h1423 | h1423
                                · rcases p1419_3 (m.d 1 3) (by simp) with h1424 | h1424
                                  · linarith only [h1, h1424, hlam]
                                  · linarith only [h1385, h1424, hlam]
                                · linarith only [h1423, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                rcases p1419_3 (m.d 0 3) (by simp) with h1428 | h1428
                                · rcases p1419_3 (m.d 1 3) (by simp) with h1429 | h1429
                                  · linarith only [h1, h1429, hlam]
                                  · linarith only [h1386, h1429, hlam]
                                · linarith only [h1428, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h9, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1401_1, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1399, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1401_1, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h4, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h4, hlam, p1401_2, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h1399, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h6, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1385, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1395, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1399, hlam, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h7, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1386, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h1396, hlam, p1419_0]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                              · have p1419_0 := h1419c.1
                                have p1419_1 := h1419c.2.1
                                have p1419_2 := h1419c.2.2.1
                                have p1419_3 := h1419c.2.2.2
                                linarith only [hlam, p1419_0]
                    · linarith only [h1410, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1454 | h1454
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1455 | h1455
                      · linarith only [h0, h1455, hlam]
                      · linarith only [h1383, h1455, hlam]
                    · linarith only [h1454, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1459 | h1459
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1460 | h1460
                      · linarith only [h0, h1460, hlam]
                      · linarith only [h1384, h1460, hlam]
                    · linarith only [h1459, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h0, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h9, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h0, h1383, h1387, h1395, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h0, h1383, h1395, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1472 | h1472
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1473 | h1473
                      · linarith only [h1473, h9, hlam]
                      · linarith only [h1383, h1473, hlam]
                    · linarith only [h1472, h2, hlam]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    rcases p1401_3 (m.d 0 1) (by simp) with h1477 | h1477
                    · rcases p1401_3 (m.d 1 2) (by simp) with h1478 | h1478
                      · linarith only [h1478, h9, hlam]
                      · linarith only [h1384, h1478, hlam]
                    · linarith only [h1477, h3, hlam]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h2, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1383, hlam, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1385, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1387, hlam, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h3, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1384, hlam, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h1386, hlam, p1401_0]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [h0, h1383, h1384, h1395, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1401_1]
                  · have p1401_0 := h1401c.1
                    have p1401_1 := h1401c.2.1
                    have p1401_2 := h1401c.2.2.1
                    have p1401_3 := h1401c.2.2.2
                    linarith only [hlam, p1401_0]
            · linarith only [h0, h1383, h1395, h1396, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1383, h1395, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h1384, h1386, h9, hlam]
    · linarith only [h1383, h1385, h9, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1496 | h1496
    · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
        · linarith only [h1383, h1384, h1498, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1500 | h1500
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1501 | h1501
            · rcases m.htr 2 4 5 (by decide) (by decide) with h1502 | h1502
              · linarith only [h1383, h1384, h1498, h1501, h1502, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 3 4 5 (by decide) (by decide) with h1504 | h1504
                · linarith only [h1383, h1384, h1500, h1502, h1504, hlam]
                · rcases h1bigk with h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c | h1506c
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1508 | h1508
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1509 | h1509
                      · linarith only [h1509, hlam, p1506_0]
                      · rcases p1506_3 (m.d 1 3) (by simp) with h1511 | h1511
                        · linarith only [h1, h1511, hlam]
                        · linarith only [h1511, h9, hlam]
                    · linarith only [h1508, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1515 | h1515
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1516 | h1516
                      · linarith only [h0, h1516, hlam]
                      · rcases p1506_3 (m.d 1 3) (by simp) with h1518 | h1518
                        · linarith only [h1518, hlam, p1506_0]
                        · rcases p1506_3 (m.d 1 4) (by simp) with h1520 | h1520
                          · linarith only [h1520, h2, hlam]
                          · rcases p1506_3 (m.d 1 5) (by simp) with h1522 | h1522
                            · linarith only [h1522, h3, hlam]
                            · rcases h3bigk with h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c | h1524c
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h1383, h1384, h1497, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h1383, h1500, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                rcases p1524_3 (m.d 0 3) (by simp) with h1528 | h1528
                                · rcases p1524_3 (m.d 1 3) (by simp) with h1529 | h1529
                                  · linarith only [h1, h1529, hlam]
                                  · linarith only [h1496, h1529, hlam]
                                · linarith only [h1528, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                rcases p1524_3 (m.d 0 3) (by simp) with h1533 | h1533
                                · rcases p1524_3 (m.d 1 3) (by simp) with h1534 | h1534
                                  · linarith only [h1, h1534, hlam]
                                  · linarith only [h1497, h1534, hlam]
                                · linarith only [h1533, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h9, hlam, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1506_1, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1504, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1506_1, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h4, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h4, hlam, p1506_2, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h1504, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h6, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1496, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1500, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1504, hlam, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h7, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1497, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h1501, hlam, p1524_0]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [h0, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1524_1]
                              · have p1524_0 := h1524c.1
                                have p1524_1 := h1524c.2.1
                                have p1524_2 := h1524c.2.2.1
                                have p1524_3 := h1524c.2.2.2
                                linarith only [hlam, p1524_0]
                    · linarith only [h1515, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1559 | h1559
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1560 | h1560
                      · linarith only [h0, h1560, hlam]
                      · linarith only [h1383, h1560, hlam]
                    · linarith only [h1559, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1564 | h1564
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1565 | h1565
                      · linarith only [h0, h1565, hlam]
                      · rcases p1506_3 (m.d 1 3) (by simp) with h1567 | h1567
                        · linarith only [h1, h1567, hlam]
                        · linarith only [h1497, h1567, hlam]
                    · linarith only [h1564, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h0, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h9, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h0, h4, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1384, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h0, h1383, h1500, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1579 | h1579
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1580 | h1580
                      · linarith only [h1580, h9, hlam]
                      · linarith only [h1383, h1580, hlam]
                    · linarith only [h1579, h2, hlam]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h0, h1383, h1384, h1500, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h2, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1383, hlam, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1496, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1498, hlam, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h3, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1383, h1500, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1506_1]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [h1497, hlam, p1506_0]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    rcases p1506_3 (m.d 0 1) (by simp) with h1593 | h1593
                    · rcases p1506_3 (m.d 1 2) (by simp) with h1594 | h1594
                      · linarith only [h1384, h1594, hlam]
                      · linarith only [h1383, h1594, hlam]
                    · linarith only [h1593, h2, hlam]
                  · have p1506_0 := h1506c.1
                    have p1506_1 := h1506c.2.1
                    have p1506_2 := h1506c.2.2.1
                    have p1506_3 := h1506c.2.2.2
                    linarith only [hlam, p1506_0]
            · linarith only [h1497, h1501, h9, hlam]
          · linarith only [h0, h1383, h1500, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 1 4 5 (by decide) (by decide) with h1601 | h1601
        · linarith only [h1383, h1497, h1601, h9, hlam]
        · rcases m.htr 2 3 4 (by decide) (by decide) with h1603 | h1603
          · rcases m.htr 2 3 5 (by decide) (by decide) with h1604 | h1604
            · linarith only [h0, h1383, h1497, h1604, h4, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1383, h1603, h1604, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1383, h1603, h4, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h1383, h1496, h9, hlam]

set_option maxHeartbeats 5816000 in
theorem r1l7_11_23_L_I_H_I_s8_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1383 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1609 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h1610 | h1610
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1611 | h1611
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1612 | h1612
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1613 | h1613
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1614 | h1614
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1615 | h1615
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1616 | h1616
              · rcases h1bigk with h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c | h1617c
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  rcases p1617_3 (m.d 0 1) (by simp) with h1619 | h1619
                  · rcases p1617_3 (m.d 1 2) (by simp) with h1620 | h1620
                    · linarith only [h1620, hlam, p1617_0]
                    · rcases p1617_3 (m.d 1 3) (by simp) with h1622 | h1622
                      · linarith only [h1, h1622, hlam]
                      · linarith only [h1622, h9, hlam]
                  · linarith only [h1619, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1610, h1616, hc01, hc45, hlam, hphi, ht0b, ht5b, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  rcases p1617_3 (m.d 0 1) (by simp) with h1627 | h1627
                  · rcases p1617_3 (m.d 1 2) (by simp) with h1628 | h1628
                    · linarith only [h0, h1628, hlam]
                    · rcases p1617_3 (m.d 1 3) (by simp) with h1630 | h1630
                      · linarith only [h1, h1630, hlam]
                      · linarith only [h1610, h1630, hlam]
                  · linarith only [h1627, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  rcases p1617_3 (m.d 0 1) (by simp) with h1634 | h1634
                  · rcases p1617_3 (m.d 1 2) (by simp) with h1635 | h1635
                    · linarith only [h0, h1635, hlam]
                    · linarith only [h1609, h1635, hlam]
                  · linarith only [h1634, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h0, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h9, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1383, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h0, h1383, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h0, h1609, h1614, h1616, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h0, h1383, h1609, h1614, h1616, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  rcases p1617_3 (m.d 0 1) (by simp) with h1648 | h1648
                  · rcases p1617_3 (m.d 1 2) (by simp) with h1649 | h1649
                    · linarith only [h1649, h9, hlam]
                    · linarith only [h1609, h1649, hlam]
                  · linarith only [h1648, h3, hlam]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h2, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1609, h1614, h1616, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1610, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  rcases p1617_3 (m.d 0 1) (by simp) with h1657 | h1657
                  · rcases p1617_3 (m.d 1 2) (by simp) with h1658 | h1658
                    · linarith only [h1383, h1658, hlam]
                    · linarith only [h1609, h1658, hlam]
                  · linarith only [h1657, h3, hlam]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h3, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1609, hlam, p1617_1]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1611, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [h1612, hlam, p1617_0]
                · have p1617_0 := h1617c.1
                  have p1617_1 := h1617c.2.1
                  have p1617_2 := h1617c.2.2.1
                  have p1617_3 := h1617c.2.2.2
                  linarith only [hlam, p1617_0]
              · linarith only [h0, h1383, h1609, h1613, h1615, h1616, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1383, h1609, h1612, h1615, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1383, h1609, h1613, h1614, h7, hc03, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h1609, h1613, h4, h6, h9, hc02, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1383, h1609, h1612, hlam]
    · linarith only [h1609, h1611, h9, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1675 | h1675
        · linarith only [h0, h1610, h1673, h1675, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h1609, h1675, h4, h6, h9, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h1609, h1610, h1674, h9, hlam]
    · linarith only [h1609, h1673, h9, hlam]

end R2N4
