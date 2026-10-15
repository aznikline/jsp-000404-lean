import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1010 | h1010
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1011 | h1011
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1012 | h1012
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1013 | h1013
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1014 | h1014
            · linarith only [h0, h1008, h1014, h2, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1008, h1011, h1014, h2, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h1009, h1013, h7, hlam]
        · linarith only [h0, h1009, h1012, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1019 | h1019
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1020 | h1020
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1021 | h1021
            · linarith only [h0, h1008, h1011, h1021, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1023 | h1023
              · linarith only [h1008, h1011, h1019, h1023, hlam]
              · rcases h2bigk with h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c | h1025c
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  rcases p1025_3 (m.d 0 2) (by simp) with h1027 | h1027
                  · rcases p1025_3 (m.d 1 2) (by simp) with h1028 | h1028
                    · linarith only [h0, h1028, hlam]
                    · rcases p1025_3 (m.d 2 3) (by simp) with h1030 | h1030
                      · linarith only [h1030, h2, hlam]
                      · linarith only [h1030, h7, hlam]
                  · linarith only [h0, h1027, hlam]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, h1008, h1019, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1008, h2, h7, hlam, p1025_2]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1009, h2, h7, hlam, p1025_2]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, hlam, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h7, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, h2, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, h2, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h2, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, h1008, h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  rcases p1025_3 (m.d 0 2) (by simp) with h1045 | h1045
                  · rcases p1025_3 (m.d 1 2) (by simp) with h1046 | h1046
                    · linarith only [h1046, h7, hlam]
                    · linarith only [h1008, h1046, hlam]
                  · linarith only [h1045, h3, hlam]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  rcases p1025_3 (m.d 0 2) (by simp) with h1050 | h1050
                  · rcases p1025_3 (m.d 1 2) (by simp) with h1051 | h1051
                    · linarith only [h1051, h7, hlam]
                    · linarith only [h1009, h1051, hlam]
                  · linarith only [h1050, h4, hlam]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h3, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1008, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1019, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1021, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h4, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1009, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h1020, hlam, p1025_0]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [h0, h1009, h1019, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1025_1]
                · have p1025_0 := h1025c.1
                  have p1025_1 := h1025c.2.1
                  have p1025_2 := h1025c.2.2.1
                  have p1025_3 := h1025c.2.2.2
                  linarith only [hlam, p1025_0]
          · linarith only [h1009, h1020, h7, hlam]
        · linarith only [h0, h1009, h1019, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h1008, h1010, h7, hlam]
  · rcases m.htr 1 3 4 (by decide) (by decide) with h1068 | h1068
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1069 | h1069
      · linarith only [h1008, h1009, h1069, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1071 | h1071
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1072 | h1072
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1073 | h1073
            · linarith only [h1008, h1009, h1069, h1072, h1073, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1075 | h1075
              · linarith only [h1008, h1009, h1071, h1073, h1075, hlam]
              · rcases h2bigk with h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  rcases p1077_3 (m.d 0 2) (by simp) with h1079 | h1079
                  · rcases p1077_3 (m.d 1 2) (by simp) with h1080 | h1080
                    · linarith only [h0, h1080, hlam]
                    · rcases p1077_3 (m.d 2 3) (by simp) with h1082 | h1082
                      · linarith only [h1082, h2, hlam]
                      · linarith only [h1082, h7, hlam]
                  · linarith only [h0, h1079, hlam]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1008, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1008, h2, h7, hlam, p1077_2]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1008, h1009, h1071, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, hlam, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h7, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1071, h2, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1009, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h2, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1008, h1071, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  rcases p1077_3 (m.d 0 2) (by simp) with h1097 | h1097
                  · rcases p1077_3 (m.d 1 2) (by simp) with h1098 | h1098
                    · linarith only [h1098, h7, hlam]
                    · linarith only [h1008, h1098, hlam]
                  · linarith only [h1097, h3, hlam]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1008, h1009, h1071, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h3, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1008, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1071, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1073, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h4, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h0, h1008, h1071, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [h1072, hlam, p1077_0]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  rcases p1077_3 (m.d 0 2) (by simp) with h1111 | h1111
                  · rcases p1077_3 (m.d 1 2) (by simp) with h1112 | h1112
                    · linarith only [h1009, h1112, hlam]
                    · linarith only [h1008, h1112, hlam]
                  · linarith only [h1111, h3, hlam]
                · have p1077_0 := h1077c.1
                  have p1077_1 := h1077c.2.1
                  have p1077_2 := h1077c.2.2.1
                  have p1077_3 := h1077c.2.2.2
                  linarith only [hlam, p1077_0]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1117 | h1117
            · linarith only [h1008, h1072, h1117, h7, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1119 | h1119
              · linarith only [h0, h1008, h1072, h1117, h1119, h2, h5, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1008, h1071, h1072, h1119, h7, hc34, hc45, hlam, hphi]
        · linarith only [h0, h1008, h1071, h2, h5, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · linarith only [h1008, h1068, h7, hlam]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1124 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 3 4 (by decide) (by decide) with h1125 | h1125
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1127 | h1127
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1128 | h1128
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1129 | h1129
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1130 | h1130
            · rcases h2bigk with h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                rcases p1131_3 (m.d 0 2) (by simp) with h1133 | h1133
                · rcases p1131_3 (m.d 1 2) (by simp) with h1134 | h1134
                  · linarith only [h0, h1134, hlam]
                  · rcases p1131_3 (m.d 2 3) (by simp) with h1136 | h1136
                    · linarith only [h1136, h2, hlam]
                    · linarith only [h1136, h7, hlam]
                · linarith only [h0, h1133, hlam]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, h1008, h1124, h1127, h1128, h1130, hc01, hc45, hlam, hphi, ht0b, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, h1008, h1124, h1128, h1130, hc01, hc45, hlam, hphi, ht0b, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1008, h1124, h1127, h2, hlam, p1131_2]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, hlam, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h7, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1008, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1008, h1127, h1128, h1130, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h2, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, h1124, h1128, h1130, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, h1008, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                rcases p1131_3 (m.d 0 2) (by simp) with h1152 | h1152
                · rcases p1131_3 (m.d 1 2) (by simp) with h1153 | h1153
                  · linarith only [h1153, h7, hlam]
                  · linarith only [h1124, h1153, hlam]
                · linarith only [h1152, h4, hlam]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h3, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h0, h1124, h1128, h1130, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1127, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                rcases p1131_3 (m.d 0 2) (by simp) with h1161 | h1161
                · rcases p1131_3 (m.d 1 2) (by simp) with h1162 | h1162
                  · linarith only [h1008, h1162, hlam]
                  · linarith only [h1124, h1162, hlam]
                · linarith only [h1161, h4, hlam]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h4, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1124, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1128, hlam, p1131_0]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [h1129, hlam, p1131_1]
              · have p1131_0 := h1131c.1
                have p1131_1 := h1131c.2.1
                have p1131_2 := h1131c.2.2.1
                have p1131_3 := h1131c.2.2.2
                linarith only [hlam, p1131_0]
            · linarith only [h0, h1008, h1124, h1127, h1129, h1130, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
          · linarith only [h0, h1008, h1124, h1129, h2, h5, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · linarith only [h1008, h1124, h1127, h1128, hlam]
      · linarith only [h0, h1124, h1127, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h1008, h1124, h1126, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1176 | h1176
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1177 | h1177
      · linarith only [h0, h1124, h1125, h1177, h2, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · linarith only [h0, h1124, h1177, h2, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
    · linarith only [h1124, h1125, h1176, h7, hlam]

set_option maxHeartbeats 5772000 in
theorem r1l7_12_24_L_I_H_I_s5_x0_x1_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h7 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1008 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1124 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1181 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 4 5 (by decide) (by decide) with h1182 | h1182
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1183 | h1183
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1184 | h1184
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1185 | h1185
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1186 | h1186
          · rcases h2bigk with h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c | h1187c
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1189 | h1189
              · rcases p1187_3 (m.d 1 2) (by simp) with h1190 | h1190
                · linarith only [h0, h1190, hlam]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1192 | h1192
                  · linarith only [h1192, h2, hlam]
                  · linarith only [h1192, h7, hlam]
              · linarith only [h0, h1189, hlam]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h0, h1181, h1186, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1197 | h1197
              · rcases p1187_3 (m.d 1 2) (by simp) with h1198 | h1198
                · linarith only [h0, h1198, hlam]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1200 | h1200
                  · linarith only [h1200, h2, hlam]
                  · linarith only [h1183, h1200, hlam]
              · linarith only [h1197, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1204 | h1204
              · rcases p1187_3 (m.d 1 2) (by simp) with h1205 | h1205
                · linarith only [h0, h1205, hlam]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1207 | h1207
                  · linarith only [h1207, h2, hlam]
                  · linarith only [h1184, h1207, hlam]
              · linarith only [h1204, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h0, hlam, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h7, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1008, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1124, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h2, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1217 | h1217
              · rcases p1187_3 (m.d 1 2) (by simp) with h1218 | h1218
                · linarith only [h1218, hlam, p1187_0]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1220 | h1220
                  · rcases p1187_3 (m.d 2 4) (by simp) with h1221 | h1221
                    · linarith only [h1183, h1221, hlam]
                    · linarith only [h1008, h1221, hlam]
                  · linarith only [h1220, hlam, p1187_0]
              · linarith only [h0, h1217, hlam]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1124, h1185, hc12, hc23, hlam, hphi, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h3, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1230 | h1230
              · rcases p1187_3 (m.d 1 2) (by simp) with h1231 | h1231
                · linarith only [h1231, hlam, p1187_0]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1233 | h1233
                  · rcases p1187_3 (m.d 2 4) (by simp) with h1234 | h1234
                    · rcases p1187_3 (m.d 2 5) (by simp) with h1235 | h1235
                      · linarith only [h1185, h1235, hlam]
                      · linarith only [h1124, h1235, hlam]
                    · linarith only [h1234, hlam, p1187_0]
                  · linarith only [h1233, h7, hlam]
              · linarith only [h0, h1230, hlam]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1183, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1124, hc12, hc24, hlam, hphi, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h4, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              rcases p1187_3 (m.d 0 2) (by simp) with h1245 | h1245
              · rcases p1187_3 (m.d 1 2) (by simp) with h1246 | h1246
                · linarith only [h1246, hlam, p1187_0]
                · rcases p1187_3 (m.d 2 3) (by simp) with h1248 | h1248
                  · rcases p1187_3 (m.d 2 4) (by simp) with h1249 | h1249
                    · rcases p1187_3 (m.d 2 5) (by simp) with h1250 | h1250
                      · rcases h4bigk with h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c | h1251c
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1181, h1186, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1008, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1186, h2, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          rcases p1251_3 (m.d 0 4) (by simp) with h1256 | h1256
                          · rcases p1251_3 (m.d 1 4) (by simp) with h1257 | h1257
                            · linarith only [h1, h1257, hlam]
                            · linarith only [h1182, h1257, hlam]
                          · linarith only [h1256, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1008, hlam, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1186, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1181, h2, h7, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h3, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1183, h1186, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h0, h1183, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h5, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1181, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1183, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1, h1181, hc01, hc45, hlam, hphi, ht0b, ht5b, p1251_1]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h6, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1182, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1185, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [h1186, hlam, p1251_0]
                        · have p1251_0 := h1251c.1
                          have p1251_1 := h1251c.2.1
                          have p1251_2 := h1251c.2.2.1
                          have p1251_3 := h1251c.2.2.2
                          linarith only [hlam, p1251_0]
                      · linarith only [h1250, hlam, p1187_0]
                    · linarith only [h1008, h1249, hlam]
                  · linarith only [h1248, h7, hlam]
              · linarith only [h0, h1245, hlam]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1184, hlam, p1187_0]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [h1185, hlam, p1187_1]
            · have p1187_0 := h1187c.1
              have p1187_1 := h1187c.2.1
              have p1187_2 := h1187c.2.2.1
              have p1187_3 := h1187c.2.2.2
              linarith only [hlam, p1187_0]
          · rcases h2bigk with h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c | h1288c
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              rcases p1288_3 (m.d 0 2) (by simp) with h1290 | h1290
              · rcases p1288_3 (m.d 1 2) (by simp) with h1291 | h1291
                · linarith only [h0, h1291, hlam]
                · rcases p1288_3 (m.d 2 3) (by simp) with h1293 | h1293
                  · linarith only [h1293, h2, hlam]
                  · linarith only [h1293, h7, hlam]
              · linarith only [h0, h1290, hlam]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h0, h1008, h1182, h1183, h1186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h0, h1008, h1182, h1186, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              rcases p1288_3 (m.d 0 2) (by simp) with h1299 | h1299
              · rcases p1288_3 (m.d 1 2) (by simp) with h1300 | h1300
                · linarith only [h0, h1300, hlam]
                · rcases p1288_3 (m.d 2 3) (by simp) with h1302 | h1302
                  · linarith only [h1302, h2, hlam]
                  · linarith only [h1184, h1302, hlam]
              · linarith only [h1299, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h0, hlam, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h7, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1008, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1124, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h2, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              rcases p1288_3 (m.d 0 2) (by simp) with h1312 | h1312
              · rcases p1288_3 (m.d 1 2) (by simp) with h1313 | h1313
                · linarith only [h1313, hlam, p1288_0]
                · rcases p1288_3 (m.d 2 3) (by simp) with h1315 | h1315
                  · rcases p1288_3 (m.d 2 4) (by simp) with h1316 | h1316
                    · linarith only [h1183, h1316, hlam]
                    · linarith only [h1008, h1316, hlam]
                  · linarith only [h1315, hlam, p1288_0]
              · linarith only [h0, h1312, hlam]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1008, h1182, h1186, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h3, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              rcases p1288_3 (m.d 0 2) (by simp) with h1325 | h1325
              · rcases p1288_3 (m.d 1 2) (by simp) with h1326 | h1326
                · linarith only [h1326, hlam, p1288_0]
                · rcases p1288_3 (m.d 2 3) (by simp) with h1328 | h1328
                  · rcases p1288_3 (m.d 2 4) (by simp) with h1329 | h1329
                    · rcases p1288_3 (m.d 2 5) (by simp) with h1330 | h1330
                      · linarith only [h1185, h1330, hlam]
                      · linarith only [h1124, h1330, hlam]
                    · linarith only [h1329, hlam, p1288_0]
                  · linarith only [h1328, h7, hlam]
              · linarith only [h0, h1325, hlam]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1183, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1124, hc12, hc24, hlam, hphi, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h4, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              rcases p1288_3 (m.d 0 2) (by simp) with h1340 | h1340
              · rcases p1288_3 (m.d 1 2) (by simp) with h1341 | h1341
                · linarith only [h1341, hlam, p1288_0]
                · rcases p1288_3 (m.d 2 3) (by simp) with h1343 | h1343
                  · rcases p1288_3 (m.d 2 4) (by simp) with h1344 | h1344
                    · rcases p1288_3 (m.d 2 5) (by simp) with h1345 | h1345
                      · rcases h4bigk with h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c | h1346c
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1182, h1186, h2, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1008, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          rcases p1346_3 (m.d 0 4) (by simp) with h1350 | h1350
                          · rcases p1346_3 (m.d 1 4) (by simp) with h1351 | h1351
                            · linarith only [h1, h1351, hlam]
                            · linarith only [h1181, h1351, hlam]
                          · linarith only [h1350, h5, hlam]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1186, h2, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1008, hlam, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1181, h1186, h2, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h3, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1183, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h0, h1183, h1186, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h5, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1181, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1183, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1186, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h6, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1182, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1185, hlam, p1346_0]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [h1182, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1346_1]
                        · have p1346_0 := h1346c.1
                          have p1346_1 := h1346c.2.1
                          have p1346_2 := h1346c.2.2.1
                          have p1346_3 := h1346c.2.2.2
                          linarith only [hlam, p1346_0]
                      · linarith only [h1345, hlam, p1288_0]
                    · linarith only [h1008, h1344, hlam]
                  · linarith only [h1343, h7, hlam]
              · linarith only [h0, h1340, hlam]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1184, hlam, p1288_0]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [h1185, hlam, p1288_1]
            · have p1288_0 := h1288c.1
              have p1288_1 := h1288c.2.1
              have p1288_2 := h1288c.2.2.1
              have p1288_3 := h1288c.2.2.2
              linarith only [hlam, p1288_0]
        · linarith only [h1008, h1182, h1185, hlam]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1384 | h1384
        · linarith only [h1183, h1184, h1384, hlam]
        · linarith only [h1008, h1182, h1384, hlam]
    · linarith only [h1181, h1183, h7, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h1388 | h1388
    · rcases m.htr 2 3 5 (by decide) (by decide) with h1389 | h1389
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1390 | h1390
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1391 | h1391
          · linarith only [h1181, h1182, h1391, hlam]
          · rcases h2bigk with h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c | h1393c
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1008, h1182, h1388, h1390, h2, hlam, p1393_2]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1008, h1182, h1388, h1390, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h0, h1008, h1182, h1390, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              rcases p1393_3 (m.d 0 2) (by simp) with h1398 | h1398
              · rcases p1393_3 (m.d 1 2) (by simp) with h1399 | h1399
                · linarith only [h0, h1399, hlam]
                · rcases p1393_3 (m.d 2 3) (by simp) with h1401 | h1401
                  · linarith only [h1401, h2, hlam]
                  · linarith only [h1389, h1401, hlam]
              · linarith only [h1398, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h0, hlam, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h7, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1008, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1124, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h2, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              rcases p1393_3 (m.d 0 2) (by simp) with h1411 | h1411
              · rcases p1393_3 (m.d 1 2) (by simp) with h1412 | h1412
                · linarith only [h1412, hlam, p1393_0]
                · rcases p1393_3 (m.d 2 3) (by simp) with h1414 | h1414
                  · rcases p1393_3 (m.d 2 4) (by simp) with h1415 | h1415
                    · linarith only [h1388, h1415, hlam]
                    · linarith only [h1008, h1415, hlam]
                  · linarith only [h1414, hlam, p1393_0]
              · linarith only [h0, h1411, hlam]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1008, h1182, h1390, hc12, hc23, hlam, hphi, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h3, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              rcases p1393_3 (m.d 0 2) (by simp) with h1424 | h1424
              · rcases p1393_3 (m.d 1 2) (by simp) with h1425 | h1425
                · linarith only [h1425, hlam, p1393_0]
                · rcases p1393_3 (m.d 2 3) (by simp) with h1427 | h1427
                  · rcases p1393_3 (m.d 2 4) (by simp) with h1428 | h1428
                    · rcases p1393_3 (m.d 2 5) (by simp) with h1429 | h1429
                      · linarith only [h1390, h1429, hlam]
                      · linarith only [h1124, h1429, hlam]
                    · linarith only [h1428, hlam, p1393_0]
                  · linarith only [h1427, h7, hlam]
              · linarith only [h0, h1424, hlam]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1388, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1008, h1182, h1390, hc12, hc24, hlam, hphi, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h4, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              rcases p1393_3 (m.d 0 2) (by simp) with h1439 | h1439
              · rcases p1393_3 (m.d 1 2) (by simp) with h1440 | h1440
                · linarith only [h1440, hlam, p1393_0]
                · rcases p1393_3 (m.d 2 3) (by simp) with h1442 | h1442
                  · rcases p1393_3 (m.d 2 4) (by simp) with h1443 | h1443
                    · rcases p1393_3 (m.d 2 5) (by simp) with h1444 | h1444
                      · rcases h4bigk with h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c | h1445c
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          rcases p1445_3 (m.d 0 4) (by simp) with h1447 | h1447
                          · rcases p1445_3 (m.d 1 4) (by simp) with h1448 | h1448
                            · linarith only [h1, h1448, hlam]
                            · rcases p1445_3 (m.d 2 4) (by simp) with h1450 | h1450
                              · linarith only [h1450, h3, hlam]
                              · linarith only [h1008, h1450, hlam]
                          · linarith only [h1, h1447, hlam]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h1008, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          rcases p1445_3 (m.d 0 4) (by simp) with h1455 | h1455
                          · rcases p1445_3 (m.d 1 4) (by simp) with h1456 | h1456
                            · linarith only [h1, h1456, hlam]
                            · linarith only [h1181, h1456, hlam]
                          · linarith only [h1455, h5, hlam]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h1008, h1182, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1008, hlam, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1182, h1390, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1182, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h3, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h1388, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h1008, h1182, h1388, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h5, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1181, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1388, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1391, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h6, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1008, hc12, hc45, hlam, hphi, ht23, ht34, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h1390, hlam, p1445_0]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [h0, h1388, h1390, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1445_1]
                        · have p1445_0 := h1445c.1
                          have p1445_1 := h1445c.2.1
                          have p1445_2 := h1445c.2.2.1
                          have p1445_3 := h1445c.2.2.2
                          linarith only [hlam, p1445_0]
                      · linarith only [h1444, hlam, p1393_0]
                    · linarith only [h1008, h1443, hlam]
                  · linarith only [h1442, h7, hlam]
              · linarith only [h0, h1439, hlam]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1389, hlam, p1393_0]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [h1390, hlam, p1393_1]
            · have p1393_0 := h1393c.1
              have p1393_1 := h1393c.2.1
              have p1393_2 := h1393c.2.2.1
              have p1393_3 := h1393c.2.2.2
              linarith only [hlam, p1393_0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1488 | h1488
          · linarith only [h0, h1008, h1390, h1488, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h2bigk with h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1008, h1390, h2, h5, h6, hlam, p1490_2]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              rcases p1490_3 (m.d 0 2) (by simp) with h1493 | h1493
              · rcases p1490_3 (m.d 1 2) (by simp) with h1494 | h1494
                · linarith only [h0, h1494, hlam]
                · rcases p1490_3 (m.d 2 3) (by simp) with h1496 | h1496
                  · linarith only [h1496, hlam, p1490_0]
                  · rcases p1490_3 (m.d 2 4) (by simp) with h1498 | h1498
                    · linarith only [h1498, h3, hlam]
                    · rcases p1490_3 (m.d 2 5) (by simp) with h1500 | h1500
                      · linarith only [h1500, h4, hlam]
                      · rcases h4bigk with h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c | h1502c
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          rcases p1502_3 (m.d 0 4) (by simp) with h1504 | h1504
                          · rcases p1502_3 (m.d 1 4) (by simp) with h1505 | h1505
                            · linarith only [h1, h1505, hlam]
                            · rcases p1502_3 (m.d 2 4) (by simp) with h1507 | h1507
                              · linarith only [h1507, h3, hlam]
                              · linarith only [h1008, h1507, hlam]
                          · linarith only [h1, h1504, hlam]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1008, h2, h5, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          rcases p1502_3 (m.d 0 4) (by simp) with h1512 | h1512
                          · rcases p1502_3 (m.d 1 4) (by simp) with h1513 | h1513
                            · linarith only [h1, h1513, hlam]
                            · linarith only [h1181, h1513, hlam]
                          · linarith only [h1512, h5, hlam]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h0, h1008, h1390, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1008, hlam, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1182, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h3, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1390, h6, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h0, h1389, h1390, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1490_1, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1390, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h5, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1181, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1388, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1488, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h6, hlam, p1502_0]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h1008, hc12, hc45, hlam, hphi, ht23, ht34, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1502_1]
                        · have p1502_0 := h1502c.1
                          have p1502_1 := h1502c.2.1
                          have p1502_2 := h1502c.2.2.1
                          have p1502_3 := h1502c.2.2.2
                          linarith only [hlam, p1502_0]
              · linarith only [h1493, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              rcases p1490_3 (m.d 0 2) (by simp) with h1539 | h1539
              · rcases p1490_3 (m.d 1 2) (by simp) with h1540 | h1540
                · linarith only [h0, h1540, hlam]
                · rcases p1490_3 (m.d 2 3) (by simp) with h1542 | h1542
                  · linarith only [h1542, h2, hlam]
                  · linarith only [h1388, h1542, hlam]
              · linarith only [h1539, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              rcases p1490_3 (m.d 0 2) (by simp) with h1546 | h1546
              · rcases p1490_3 (m.d 1 2) (by simp) with h1547 | h1547
                · linarith only [h0, h1547, hlam]
                · rcases p1490_3 (m.d 2 3) (by simp) with h1549 | h1549
                  · linarith only [h1549, h2, hlam]
                  · linarith only [h1389, h1549, hlam]
              · linarith only [h1546, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h0, hlam, p1490_1]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h7, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1008, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1124, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h2, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              rcases p1490_3 (m.d 0 2) (by simp) with h1559 | h1559
              · rcases p1490_3 (m.d 1 2) (by simp) with h1560 | h1560
                · linarith only [h1560, hlam, p1490_0]
                · rcases p1490_3 (m.d 2 3) (by simp) with h1562 | h1562
                  · rcases p1490_3 (m.d 2 4) (by simp) with h1563 | h1563
                    · linarith only [h1388, h1563, hlam]
                    · linarith only [h1008, h1563, hlam]
                  · linarith only [h1562, hlam, p1490_0]
              · linarith only [h0, h1559, hlam]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1008, hc12, hc23, hlam, hphi, p1490_1]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h0, h1124, h2, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1490_1]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h3, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h0, h1390, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1490_1]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1388, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1390, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h4, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              rcases p1490_3 (m.d 0 2) (by simp) with h1577 | h1577
              · rcases p1490_3 (m.d 1 2) (by simp) with h1578 | h1578
                · linarith only [h1578, hlam, p1490_0]
                · rcases p1490_3 (m.d 2 3) (by simp) with h1580 | h1580
                  · rcases p1490_3 (m.d 2 4) (by simp) with h1581 | h1581
                    · linarith only [h1390, h1581, hlam]
                    · linarith only [h1008, h1581, hlam]
                  · linarith only [h1580, h7, hlam]
              · linarith only [h0, h1577, hlam]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1389, hlam, p1490_0]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [h1008, hc12, hc25, hlam, hphi, p1490_1]
            · have p1490_0 := h1490c.1
              have p1490_1 := h1490c.2.1
              have p1490_2 := h1490c.2.2.1
              have p1490_3 := h1490c.2.2.2
              linarith only [hlam, p1490_0]
      · rcases m.htr 2 4 5 (by decide) (by decide) with h1589 | h1589
        · linarith only [h1008, h1182, h1388, h1389, h1589, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h1591 | h1591
          · linarith only [h1008, h1589, h1591, hc12, hc34, hlam, hphi, ht23]
          · rcases h2bigk with h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c | h1593c
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1008, h1388, h1389, h1591, h2, h5, h6, hlam, p1593_2]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              rcases p1593_3 (m.d 0 2) (by simp) with h1596 | h1596
              · rcases p1593_3 (m.d 1 2) (by simp) with h1597 | h1597
                · linarith only [h0, h1597, hlam]
                · rcases p1593_3 (m.d 2 3) (by simp) with h1599 | h1599
                  · linarith only [h1599, hlam, p1593_0]
                  · rcases p1593_3 (m.d 2 4) (by simp) with h1601 | h1601
                    · linarith only [h1601, h3, hlam]
                    · rcases p1593_3 (m.d 2 5) (by simp) with h1603 | h1603
                      · linarith only [h1603, h4, hlam]
                      · linarith only [h1389, h1603, hlam]
              · linarith only [h1596, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              rcases p1593_3 (m.d 0 2) (by simp) with h1607 | h1607
              · rcases p1593_3 (m.d 1 2) (by simp) with h1608 | h1608
                · linarith only [h0, h1608, hlam]
                · rcases p1593_3 (m.d 2 3) (by simp) with h1610 | h1610
                  · linarith only [h1610, h2, hlam]
                  · linarith only [h1388, h1610, hlam]
              · linarith only [h1607, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              rcases p1593_3 (m.d 0 2) (by simp) with h1614 | h1614
              · rcases p1593_3 (m.d 1 2) (by simp) with h1615 | h1615
                · linarith only [h0, h1615, hlam]
                · rcases p1593_3 (m.d 2 3) (by simp) with h1617 | h1617
                  · linarith only [h1617, h2, hlam]
                  · rcases p1593_3 (m.d 2 4) (by simp) with h1619 | h1619
                    · linarith only [h1619, h3, hlam]
                    · rcases p1593_3 (m.d 2 5) (by simp) with h1621 | h1621
                      · linarith only [h1621, hlam, p1593_0]
                      · rcases h4bigk with h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c | h1623c
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          rcases p1623_3 (m.d 0 4) (by simp) with h1625 | h1625
                          · rcases p1623_3 (m.d 1 4) (by simp) with h1626 | h1626
                            · linarith only [h1, h1626, hlam]
                            · rcases p1623_3 (m.d 2 4) (by simp) with h1628 | h1628
                              · linarith only [h1628, h3, hlam]
                              · linarith only [h1008, h1628, hlam]
                          · linarith only [h1, h1625, hlam]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h1008, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          rcases p1623_3 (m.d 0 4) (by simp) with h1633 | h1633
                          · rcases p1623_3 (m.d 1 4) (by simp) with h1634 | h1634
                            · linarith only [h1, h1634, hlam]
                            · linarith only [h1181, h1634, hlam]
                          · linarith only [h1633, h5, hlam]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h1008, h1388, h1389, h1591, h2, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1008, hlam, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1182, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h3, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1388, h1389, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h1388, h1389, h1591, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1589, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h5, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1181, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1388, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h1591, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h6, hlam, p1623_0]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h1008, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1623_1]
                        · have p1623_0 := h1623c.1
                          have p1623_1 := h1623c.2.1
                          have p1623_2 := h1623c.2.2.1
                          have p1623_3 := h1623c.2.2.2
                          linarith only [hlam, p1623_0]
              · linarith only [h1614, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, hlam, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h7, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1008, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1124, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h2, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, h1389, h1591, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, h1008, h1389, h1591, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1389, hlam, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h3, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, h1388, h1389, h1591, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1388, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h1589, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h4, hlam, p1593_0]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              rcases p1593_3 (m.d 0 2) (by simp) with h1676 | h1676
              · rcases p1593_3 (m.d 1 2) (by simp) with h1677 | h1677
                · linarith only [h1677, hlam, p1593_0]
                · rcases p1593_3 (m.d 2 3) (by simp) with h1679 | h1679
                  · linarith only [h1389, h1679, hlam]
                  · linarith only [h1679, h7, hlam]
              · linarith only [h0, h1676, hlam]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [h0, h1008, h1389, h1591, h2, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1593_1]
            · have p1593_0 := h1593c.1
              have p1593_1 := h1593c.2.1
              have p1593_2 := h1593c.2.2.1
              have p1593_3 := h1593c.2.2.2
              linarith only [hlam, p1593_0]
    · linarith only [h1181, h1388, h7, hlam]

end R2N4
