import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_5S5
import Jsp000404.R1LeavesN7_5S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1049 | h1049
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1050 | h1050
    · linarith only [h1050, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1052 | h1052
      · linarith only [h1052, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1054 | h1054
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1055 | h1055
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1056 | h1056
            · linarith only [h0, h1056, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1058 | h1058
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1059 | h1059
                · linarith only [h1, h1050, h1059, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1061 | h1061
                  · linarith only [h1052, h1061, h2, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1063 | h1063
                    · linarith only [h0, h1054, h1063, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h1050, h1058, h1063, hc23, hc35, hlam, hphi]
              · linarith only [h1049, h1050, h1058, hc13, hc35, hlam, hphi]
          · linarith only [h1055, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h1054, h4, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
    · linarith only [h1049, h1069, h5, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1071 | h1071
      · linarith only [h1071, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1074 | h1074
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1075 | h1075
            · linarith only [h0, h1075, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1077 | h1077
              · linarith only [h1, h1049, h1077, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1079 | h1079
                · linarith only [h1, h1069, h1079, h4, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1081 | h1081
                  · linarith only [h1049, h1071, h1074, h1075, h1081, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1083 | h1083
                    · linarith only [h1, h1049, h1073, h1083, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1085 | h1085
                      · linarith only [h1069, h1085, h4, h6, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1087 | h1087
                        · linarith only [h0, h1049, h1071, h1074, h1087, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1089 | h1089
                          · linarith only [h1087, h1089, h4, h6, hc23, hc34, hlam, hphi]
                          · rcases h0bigk with h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c | h1091c
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h0, h1074, h1083, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u0elo0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              rcases p1091_3 (m.d 0 1) (by simp) with h1094 | h1094
                              · rcases p1091_3 (m.d 0 2) (by simp) with h1095 | h1095
                                · linarith only [h0, h1095, hlam]
                                · linarith only [h1095, h4, hlam]
                              · linarith only [h1, h1094, hlam]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              rcases p1091_3 (m.d 0 1) (by simp) with h1099 | h1099
                              · rcases p1091_3 (m.d 0 2) (by simp) with h1100 | h1100
                                · linarith only [h0, h1100, hlam]
                                · linarith only [h1100, h5, hlam]
                              · linarith only [h1099, h2, hlam]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h0, h1074, h1083, h6, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u0elo0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h0, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1, h1073, h1085, h6, hc23, hc35, hlam, hphi, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1, h1049, h1073, h1085, h6, hc23, hc35, hlam, hphi, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h6, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1, hlam, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h4, hlam, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1049, hlam, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1069, hlam, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h2, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h5, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1, h1073, h1085, h5, h6, hc23, hc35, hlam, hphi, p1091_1]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h1071, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h3, hlam, p1091_0]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [h0, h1074, h1083, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1091_1, u0elo4]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              rcases p1091_3 (m.d 0 1) (by simp) with h1122 | h1122
                              · rcases p1091_3 (m.d 0 2) (by simp) with h1123 | h1123
                                · linarith only [h1123, h6, hlam]
                                · linarith only [h1123, h4, hlam]
                              · linarith only [h1, h1122, hlam]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              rcases p1091_3 (m.d 0 1) (by simp) with h1127 | h1127
                              · rcases p1091_3 (m.d 0 2) (by simp) with h1128 | h1128
                                · linarith only [h1128, h6, hlam]
                                · linarith only [h1128, h5, hlam]
                              · linarith only [h1127, h2, hlam]
                            · have p1091_0 := h1091c.1
                              have p1091_1 := h1091c.2.1
                              have p1091_2 := h1091c.2.2.1
                              have p1091_3 := h1091c.2.2.2
                              linarith only [hlam, p1091_0]
          · linarith only [h1074, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h1073, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1135 | h1135
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1136 | h1136
    · linarith only [h1136, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1138 | h1138
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1139 | h1139
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1140 | h1140
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1141 | h1141
            · linarith only [h0, h1141, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1143 | h1143
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
                · linarith only [h1, h1136, h1138, h1144, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1147 | h1147
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1148 | h1148
                      · linarith only [h0, h1, h1136, h1140, h1146, h1148, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1150 | h1150
                        · linarith only [h1140, h1141, h1150, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h1146, h1150, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1136, h1138, h1139, h1140, h1141, h1147, hc23, hc34, hlam, hphi]
                  · linarith only [h1136, h1138, h1146, hc13, hc34, hlam, hphi]
              · linarith only [h1135, h1140, h1143, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h1140, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1138, h1139, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1158 | h1158
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1160 | h1160
            · linarith only [h0, h1160, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1162 | h1162
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1163 | h1163
                · linarith only [h0, h1, h1136, h1138, h1159, h1163, h5, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1165 | h1165
                  · linarith only [h1, h1138, h1165, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1167 | h1167
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1168 | h1168
                      · linarith only [h0, h1136, h1159, h1168, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1170 | h1170
                        · linarith only [h1138, h1159, h1165, h1170, h3, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1172 | h1172
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1173 | h1173
                            · rcases h0bigk with h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h0, h1162, h1170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1174_1, u0elo0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                rcases p1174_3 (m.d 0 1) (by simp) with h1177 | h1177
                                · rcases p1174_3 (m.d 0 2) (by simp) with h1178 | h1178
                                  · linarith only [h0, h1178, hlam]
                                  · linarith only [h1178, h4, hlam]
                                · linarith only [h1, h1177, hlam]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h0, h1162, h1170, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1174_1, u0elo0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                rcases p1174_3 (m.d 0 1) (by simp) with h1183 | h1183
                                · rcases p1174_3 (m.d 0 2) (by simp) with h1184 | h1184
                                  · linarith only [h0, h1184, hlam]
                                  · linarith only [h1135, h1184, hlam]
                                · linarith only [h1183, h3, hlam]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h0, hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1, h1168, h5, hc13, hc34, hlam, hphi, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h5, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1135, h1168, h1170, h5, hc23, hc34, hlam, hphi, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h4, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1136, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1138, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h2, hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h0, h1162, h1170, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1174_1, u0elo3]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                rcases p1174_3 (m.d 0 1) (by simp) with h1200 | h1200
                                · rcases p1174_3 (m.d 0 2) (by simp) with h1201 | h1201
                                  · linarith only [h1201, h5, hlam]
                                  · linarith only [h1201, h4, hlam]
                                · linarith only [h1, h1200, hlam]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                rcases p1174_3 (m.d 0 1) (by simp) with h1206 | h1206
                                · rcases p1174_3 (m.d 0 2) (by simp) with h1207 | h1207
                                  · linarith only [h1207, h5, hlam]
                                  · linarith only [h1135, h1207, hlam]
                                · linarith only [h1206, h3, hlam]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h3, hlam, p1174_0]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1135, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1, h1135, h1159, h1168, h5, hc23, hc34, hlam, hphi, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [h1158, hlam, p1174_1]
                              · have p1174_0 := h1174c.1
                                have p1174_1 := h1174c.2.1
                                have p1174_2 := h1174c.2.2.1
                                have p1174_3 := h1174c.2.2.2
                                linarith only [hlam, p1174_0]
                            · linarith only [h0, h1162, h1168, h1172, h1173, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1172, h4, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h1158, h1160, h1162, h1167, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h1135, h1159, h1162, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h1159, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1135, h1158, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1222 | h1222
    · linarith only [h1222, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1224 | h1224
      · linarith only [h1135, h1224, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1226 | h1226
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1227 | h1227
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1228 | h1228
            · linarith only [h0, h1228, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
              · linarith only [h0, h1135, h1230, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                · linarith only [h1, h1222, h1232, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1234 | h1234
                  · linarith only [h1, h1135, h1224, h1234, h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1236 | h1236
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1237 | h1237
                      · linarith only [h0, h1222, h1227, h1237, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1239 | h1239
                        · linarith only [h1135, h1224, h1227, h1230, h1236, h1239, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1241 | h1241
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1242 | h1242
                            · rcases h0bigk with h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c | h1243c
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1227, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                rcases p1243_3 (m.d 0 1) (by simp) with h1246 | h1246
                                · rcases p1243_3 (m.d 0 2) (by simp) with h1247 | h1247
                                  · linarith only [h0, h1247, hlam]
                                  · linarith only [h1247, h4, hlam]
                                · linarith only [h1, h1246, hlam]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1227, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1135, h1227, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1, h1227, h1237, h5, hc23, hc34, hlam, hphi, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h5, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1135, hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h4, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1222, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1224, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h2, hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1227, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo3]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                rcases p1243_3 (m.d 0 1) (by simp) with h1265 | h1265
                                · rcases p1243_3 (m.d 0 2) (by simp) with h1266 | h1266
                                  · linarith only [h1266, h5, hlam]
                                  · linarith only [h1266, h4, hlam]
                                · linarith only [h1, h1265, hlam]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1135, h1227, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h3, hlam, p1243_0]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h0, h1227, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1243_1, u0elo4]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                rcases p1243_3 (m.d 0 1) (by simp) with h1274 | h1274
                                · rcases p1243_3 (m.d 0 2) (by simp) with h1275 | h1275
                                  · linarith only [h1135, h1275, hlam]
                                  · linarith only [h1275, h4, hlam]
                                · linarith only [h1, h1274, hlam]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [h1226, hlam, p1243_1]
                              · have p1243_0 := h1243c.1
                                have p1243_1 := h1243c.2.1
                                have p1243_2 := h1243c.2.2.1
                                have p1243_3 := h1243c.2.2.2
                                linarith only [hlam, p1243_0]
                            · linarith only [h0, h1227, h1237, h1242, h5, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h1227, h1236, h1241, h2, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1226, h1227, h1228, h1236, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h1135, h1227, h4, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1285 | h1285
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1286 | h1286
            · linarith only [h0, h1286, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1288 | h1288
              · linarith only [h0, h1135, h1288, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1290 | h1290
                · linarith only [h1, h1222, h1290, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1292 | h1292
                  · linarith only [h1, h1224, h1292, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1294 | h1294
                    · linarith only [h1226, h1294, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1296 | h1296
                      · linarith only [h0, h1222, h1285, h1296, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1298 | h1298
                        · linarith only [h1224, h1226, h1298, h4, h5, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1300 | h1300
                          · linarith only [h0, h1226, h1285, h1296, h1300, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1285, h1300, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1285, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s4 m hb0 hb1 hb3 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 8910000 in
set_option maxHeartbeats 8910000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 9158000 in
set_option maxHeartbeats 9158000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s3 m hb0 hb1 hb3 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4459 | h4459
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4460 | h4460
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4461 | h4461
        · linarith only [h0, h3, h4461, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4463 | h4463
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4464 | h4464
            · linarith only [h1, h3, h4464, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4466 | h4466
              · linarith only [h2, h3, h4466, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4468 | h4468
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4469 | h4469
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4470 | h4470
                    · linarith only [h0, h4461, h4470, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4472 | h4472
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4473 | h4473
                        · linarith only [h0, h3, h4464, h4468, h4473, hlam]
                        · linarith only [h0, h3, h4468, h4473, hc23, hc35, hlam, hphi]
                      · linarith only [h4463, h4464, h4472, hc13, hc35, hlam, hphi]
                  · linarith only [h4460, h4468, h4469, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4459, h4461, h4468, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4479 | h4479
            · linarith only [h1, h3, h4479, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4481 | h4481
              · linarith only [h0, h3, h4460, h4481, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4483 | h4483
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4484 | h4484
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4485 | h4485
                    · linarith only [h0, h4461, h4485, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4487 | h4487
                      · linarith only [h1, h4463, h4487, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4489 | h4489
                        · linarith only [h0, h1, h3, h4463, h4479, h4484, h4489, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h0, h3, h4483, h4489, hc23, hc35, hlam, hphi]
                  · linarith only [h4460, h4483, h4484, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4459, h4461, h4483, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4494 | h4494
        · linarith only [h0, h3, h4494, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4496 | h4496
          · linarith only [h4459, h4460, h4496, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4498 | h4498
            · linarith only [h0, h3, h4459, h4498, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4500 | h4500
              · linarith only [h2, h3, h4500, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4502 | h4502
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4503 | h4503
                  · linarith only [h0, h4460, h4503, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4505 | h4505
                    · linarith only [h0, h3, h4494, h4505, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4507 | h4507
                      · linarith only [h2, h3, h4496, h4502, h4503, h4505, h4507, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4509 | h4509
                        · linarith only [h1, h3, h4498, h4509, hlam]
                        · linarith only [h2, h3, h4502, h4503, h4509, hc23, hc35, hlam, hphi]
                · linarith only [h4459, h4460, h4500, h4502, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4513 | h4513
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4514 | h4514
        · linarith only [h0, h3, h4514, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4516 | h4516
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4517 | h4517
            · linarith only [h1, h3, h4517, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4519 | h4519
              · linarith only [h1, h3, h4459, h4513, h4519, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4521 | h4521
                · linarith only [h0, h4459, h4521, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4523 | h4523
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4524 | h4524
                    · linarith only [h0, h3, h4514, h4524, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4526 | h4526
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4527 | h4527
                        · linarith only [h1, h3, h4459, h4517, h4524, h4527, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4529 | h4529
                          · linarith only [h2, h3, h4519, h4529, hlam]
                          · linarith only [h1, h3, h4521, h4523, h4529, hc24, hc45, hlam, hphi]
                      · linarith only [h4516, h4521, h4523, h4526, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                  · linarith only [h4459, h4513, h4523, hc12, hc23, hlam, hphi]
          · linarith only [h4459, h4513, h4516, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4535 | h4535
        · linarith only [h0, h3, h4535, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4537 | h4537
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4538 | h4538
            · linarith only [h1, h3, h4538, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4540 | h4540
              · linarith only [h1, h3, h4537, h4540, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4542 | h4542
                · linarith only [h0, h4459, h4542, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4544 | h4544
                  · linarith only [h0, h4513, h4544, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4546 | h4546
                    · linarith only [h0, h3, h4535, h4546, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4548 | h4548
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4549 | h4549
                        · linarith only [h1, h3, h4513, h4537, h4538, h4546, h4549, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4551 | h4551
                          · linarith only [h1, h2, h3, h4540, h4548, h4551, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                          · linarith only [h1, h3, h4548, h4551, hc34, hc45, hlam, hphi]
                      · linarith only [h4537, h4538, h4548, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4555 | h4555
            · linarith only [h1, h3, h4555, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4557 | h4557
              · linarith only [h2, h3, h4557, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4559 | h4559
                · linarith only [h0, h3, h4459, h4559, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4561 | h4561
                  · linarith only [h0, h4513, h4561, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4563 | h4563
                    · linarith only [h0, h4535, h4563, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4565 | h4565
                      · linarith only [h1, h4537, h4565, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h4567 | h4567
                        · linarith only [h0, h1, h3, h4537, h4555, h4567, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h4569 | h4569
                          · linarith only [h2, h4537, h4557, h4569, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h4571 | h4571
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4572 | h4572
                              · linarith only [h2, h3, h4559, h4565, h4567, h4572, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h4537, h4559, h4571, h4572, hc12, hc35, hlam, hphi, ht23]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h4575 | h4575
                              · linarith only [h1, h4555, h4559, h4571, h4575, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h4577 | h4577
                                · linarith only [h2, h3, h4559, h4565, h4569, h4577, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h4579 | h4579
                                  · linarith only [h0, h4459, h4571, h4577, h4579, hc12, hc34, hlam, hphi, ht23]
                                  · linarith only [h0, h4459, h4571, h4579, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 9794000 in
set_option maxHeartbeats 9794000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s2 m hb0 hb1 hb3 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h4582 | h4582
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4583 | h4583
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4584 | h4584
        · linarith only [h0, h2, h4584, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4586 | h4586
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4587 | h4587
            · linarith only [h1, h2, h4587, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4589 | h4589
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4590 | h4590
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4591 | h4591
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4592 | h4592
                    · linarith only [h0, h2, h4584, h4586, h4592, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4594 | h4594
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4595 | h4595
                        · linarith only [h0, h2, h4587, h4591, h4592, h4595, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h4591, h4595, hc23, hc34, hlam, hphi]
                      · linarith only [h4586, h4591, h4594, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h4583, h4584, h4591, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h4589, h4590, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4601 | h4601
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4602 | h4602
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4603 | h4603
                    · linarith only [h0, h4584, h4603, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4605 | h4605
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4606 | h4606
                        · linarith only [h1, h4587, h4606, hlam]
                        · linarith only [h0, h2, h4602, h4606, hc23, hc34, hlam, hphi]
                      · linarith only [h4586, h4602, h4605, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h4583, h4584, h4602, hc12, hc24, hlam, hphi]
                · linarith only [h2, h4582, h4601, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4612 | h4612
            · linarith only [h1, h2, h4612, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4614 | h4614
              · linarith only [h4583, h4586, h4614, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4616 | h4616
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4617 | h4617
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4618 | h4618
                    · linarith only [h0, h4584, h4618, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4620 | h4620
                      · linarith only [h0, h4586, h4620, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4622 | h4622
                        · linarith only [h0, h2, h4612, h4617, h4622, hlam]
                        · linarith only [h2, h4582, h4617, h4620, h4622, hc23, hc34, hlam, hphi]
                  · linarith only [h4583, h4586, h4617, hc12, hc25, hlam, hphi]
                · linarith only [h2, h4582, h4616, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4627 | h4627
        · linarith only [h0, h2, h4627, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4629 | h4629
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4630 | h4630
            · linarith only [h1, h2, h4630, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4632 | h4632
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4633 | h4633
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4634 | h4634
                  · linarith only [h0, h4583, h4634, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4636 | h4636
                    · linarith only [h0, h2, h4627, h4636, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4638 | h4638
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4639 | h4639
                        · linarith only [h1, h4583, h4630, h4639, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4641 | h4641
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4642 | h4642
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4643 | h4643
                              · linarith only [h0, h2, h4638, h4639, h4643, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4645 | h4645
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4646 | h4646
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4647 | h4647
                                    · rcases h0bigk with h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c | h4648c
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, h4638, h4645, h4647, hc45, hlam, hphi, ht0b, ht5b, p4648_1, u0elo0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, h2, h4583, h4636, h4638, h4643, h4645, h4647, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h2, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        rcases p4648_3 (m.d 0 1) (by simp) with h4653 | h4653
                                        · rcases p4648_3 (m.d 0 2) (by simp) with h4654 | h4654
                                          · linarith only [h0, h4654, hlam]
                                          · linarith only [h4629, h4654, hlam]
                                        · linarith only [h4582, h4653, hlam]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4583, hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4627, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4582, h4583, h4643, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h1, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, h4638, h4645, h4647, hc45, hlam, hphi, ht0b, ht5b, p4648_1, u0elo2]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4630, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        rcases p4648_3 (m.d 0 1) (by simp) with h4667 | h4667
                                        · rcases p4648_3 (m.d 0 2) (by simp) with h4668 | h4668
                                          · linarith only [h4583, h4668, hlam]
                                          · linarith only [h4629, h4668, hlam]
                                        · linarith only [h4582, h4667, hlam]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, h4638, h4645, h4647, hc45, hlam, hphi, ht0b, ht5b, p4648_1, u0elo3]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h0, h4638, h4645, h4647, hc45, hlam, hphi, ht0b, ht5b, p4648_1, u0elo3]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h1, h4634, h4638, h4645, h4647, hc45, hlam, hphi, ht0b, ht5b, p4648_1, u0elo3]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        rcases p4648_3 (m.d 0 1) (by simp) with h4676 | h4676
                                        · linarith only [h2, h4676, hlam]
                                        · linarith only [h4582, h4676, hlam]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4582, hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4629, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4632, hlam, p4648_0]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [h4633, hlam, p4648_1]
                                      · have p4648_0 := h4648c.1
                                        have p4648_1 := h4648c.2.1
                                        have p4648_2 := h4648c.2.2.1
                                        have p4648_3 := h4648c.2.2.2
                                        linarith only [hlam, p4648_0]
                                    · linarith only [h4583, h4643, h4647, hc02, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h1, h2, h4582, h4634, h4636, h4638, h4642, h4645, h4646, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                                · linarith only [h4583, h4632, h4645, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h2, h4634, h4638, h4642, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h1, h4632, h4634, h4638, h4641, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1, h2, h4583, h4629, h4636, h4638, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h4583, h4629, h4633, hlam]
              · linarith only [h4583, h4629, h4632, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4692 | h4692
            · linarith only [h1, h2, h4692, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4694 | h4694
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4695 | h4695
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4696 | h4696
                  · linarith only [h0, h4583, h4696, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4698 | h4698
                    · linarith only [h0, h4627, h4698, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4700 | h4700
                      · linarith only [h0, h4629, h4700, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4702 | h4702
                        · linarith only [h1, h2, h4692, h4698, h4702, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4704 | h4704
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4705 | h4705
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4706 | h4706
                              · linarith only [h0, h2, h4702, h4706, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4708 | h4708
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4709 | h4709
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4710 | h4710
                                    · rcases h0bigk with h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c | h4711c
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h0, h2, h4698, h4706, hc12, hc34, hlam, hphi, ht23, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h1, h2, h4704, h4710, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h2, hlam, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h2, h4582, h4698, h4700, h4706, hc12, hc34, hlam, hphi, ht23, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h0, hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4583, hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4627, hlam, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4629, hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h1, hlam, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h0, h4583, h4706, hc12, hc34, hlam, hphi, ht23, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4692, hlam, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4582, h4583, h4700, h4706, hc12, hc34, hlam, hphi, ht23, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4711_1, u0elo3]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        rcases p4711_3 (m.d 0 1) (by simp) with h4728 | h4728
                                        · linarith only [h2, h4728, hlam]
                                        · linarith only [h0, h4728, hlam]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h1, h4704, h4710, hc45, hlam, hphi, ht0b, ht5b, p4711_1, u0elo3]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        rcases p4711_3 (m.d 0 1) (by simp) with h4733 | h4733
                                        · linarith only [h2, h4733, hlam]
                                        · linarith only [h4582, h4733, hlam]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4582, hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h0, h2, h4582, h4698, h4706, hc12, hc34, hlam, hphi, ht23, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4694, hlam, p4711_0]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [h4695, hlam, p4711_1]
                                      · have p4711_0 := h4711c.1
                                        have p4711_1 := h4711c.2.1
                                        have p4711_2 := h4711c.2.2.1
                                        have p4711_3 := h4711c.2.2.2
                                        linarith only [hlam, p4711_0]
                                    · linarith only [h1, h2, h4698, h4704, h4706, h4710, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                  · linarith only [h1, h2, h4698, h4704, h4705, h4709, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · linarith only [h1, h4704, h4708, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · linarith only [h2, h4695, h4705, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                          · linarith only [h1, h2, h4694, h4702, h4704, hc13, hc34, hlam, hphi]
                · linarith only [h1, h2, h4694, h4695, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4747 | h4747
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4748 | h4748
                  · linarith only [h0, h4583, h4748, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4750 | h4750
                    · linarith only [h0, h4627, h4750, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4752 | h4752
                      · linarith only [h1, h4629, h4694, h4748, h4752, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4754 | h4754
                        · linarith only [h0, h1, h2, h4692, h4694, h4754, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4756 | h4756
                          · linarith only [h1, h4583, h4694, h4756, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4758 | h4758
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4759 | h4759
                              · linarith only [h0, h2, h4754, h4759, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4761 | h4761
                                · linarith only [h0, h4583, h4694, h4759, h4761, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4763 | h4763
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4764 | h4764
                                    · rcases h0bigk with h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c | h4765c
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, h2, h4750, h4759, hc12, hc34, hlam, hphi, ht23, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, h2, h4583, h4750, h4759, hc12, hc34, hlam, hphi, ht23, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h2, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, h2, h4583, h4694, h4750, h4759, hc12, hc34, hlam, hphi, ht23, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4583, hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4627, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4629, hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h1, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, h4583, h4761, h4764, hc12, hc34, hlam, hphi, ht23, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4692, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4694, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4582, hc15, hlam, hphi, ht0b, ht5b, p4765_1, u0elo3]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        rcases p4765_3 (m.d 0 1) (by simp) with h4782 | h4782
                                        · linarith only [h2, h4782, hlam]
                                        · linarith only [h0, h4782, hlam]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        rcases p4765_3 (m.d 0 1) (by simp) with h4785 | h4785
                                        · linarith only [h2, h4785, hlam]
                                        · linarith only [h1, h4785, hlam]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        rcases p4765_3 (m.d 0 1) (by simp) with h4789 | h4789
                                        · linarith only [h2, h4789, hlam]
                                        · linarith only [h4582, h4789, hlam]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4582, hlam, p4765_0]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h0, h2, h4582, h4750, h4759, hc12, hc34, hlam, hphi, ht23, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h2, h4582, h4750, h4759, hc03, hc34, hlam, hphi, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [h4747, hlam, p4765_1]
                                      · have p4765_0 := h4765c.1
                                        have p4765_1 := h4765c.2.1
                                        have p4765_2 := h4765c.2.2.1
                                        have p4765_3 := h4765c.2.2.2
                                        linarith only [hlam, p4765_0]
                                    · linarith only [h0, h2, h4750, h4759, h4764, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h2, h4582, h4750, h4758, h4763, hlam]
                            · linarith only [h2, h4582, h4748, h4756, h4758, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h4582, h4747, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h4801 | h4801
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4802 | h4802
        · linarith only [h0, h2, h4802, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4804 | h4804
          · linarith only [h0, h4582, h4804, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4806 | h4806
            · linarith only [h1, h2, h4806, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4808 | h4808
              · linarith only [h0, h4582, h4801, h4808, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4810 | h4810
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4811 | h4811
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4812 | h4812
                    · linarith only [h0, h4802, h4812, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4814 | h4814
                      · linarith only [h0, h4582, h4804, h4814, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4816 | h4816
                        · linarith only [h0, h2, h4806, h4810, h4811, h4812, h4816, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h2, h4811, h4816, hc23, hc34, hlam, hphi]
                  · linarith only [h4801, h4802, h4811, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4820 | h4820
                  · linarith only [h0, h2, h4810, h4820, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h4801, h4810, h4820, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4823 | h4823
        · linarith only [h0, h2, h4823, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4825 | h4825
          · linarith only [h1, h4582, h4801, h4825, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h4827 | h4827
            · linarith only [h1, h2, h4827, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h4829 | h4829
              · linarith only [h1, h4582, h4829, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h4831 | h4831
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4832 | h4832
                  · linarith only [h0, h4801, h4832, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4834 | h4834
                    · linarith only [h0, h4582, h4823, h4831, h4834, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4836 | h4836
                      · linarith only [h1, h2, h4825, h4832, h4834, h4836, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4838 | h4838
                        · linarith only [h1, h2, h4827, h4834, h4838, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4840 | h4840
                          · linarith only [h1, h4582, h4829, h4840, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4842 | h4842
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h4843 | h4843
                              · linarith only [h0, h4582, h4838, h4842, h4843, hc12, hc23, hlam, hphi]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h4845 | h4845
                                · linarith only [h1, h4582, h4832, h4840, h4843, h4845, hc12, hc34, hlam, hphi, ht23]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h4847 | h4847
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h4848 | h4848
                                    · rcases h0bigk with h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c | h4849c
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h0, h4582, h4836, hc12, hc25, hlam, hphi, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h0, h4582, h4801, h4836, hc12, hc25, hlam, hphi, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h2, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4582, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h0, hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4801, hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4823, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4825, hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h1, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h0, h1, h4582, h4836, hc12, hc25, hlam, hphi, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4827, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4829, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4849_1, u0elo3]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        rcases p4849_3 (m.d 0 1) (by simp) with h4866 | h4866
                                        · linarith only [h2, h4866, hlam]
                                        · linarith only [h0, h4866, hlam]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        rcases p4849_3 (m.d 0 1) (by simp) with h4869 | h4869
                                        · linarith only [h2, h4869, hlam]
                                        · linarith only [h1, h4869, hlam]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [hlam, p4849_0]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h1, h4582, h4832, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4849_1, u0elo3]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h1, h4832, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p4849_1, u0elo4]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        rcases p4849_3 (m.d 0 1) (by simp) with h4875 | h4875
                                        · linarith only [h4582, h4875, hlam]
                                        · linarith only [h0, h4875, hlam]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        rcases p4849_3 (m.d 0 1) (by simp) with h4878 | h4878
                                        · linarith only [h4582, h4878, hlam]
                                        · linarith only [h1, h4878, hlam]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [h4831, hlam, p4849_1]
                                      · have p4849_0 := h4849c.1
                                        have p4849_1 := h4849c.2.1
                                        have p4849_2 := h4849c.2.2.1
                                        have p4849_3 := h4849c.2.2.2
                                        linarith only [hlam, p4849_0]
                                    · linarith only [h1, h2, h4831, h4832, h4834, h4843, h4848, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                  · linarith only [h2, h4831, h4834, h4847, hlam]
                            · linarith only [h2, h4831, h4842, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h4886 | h4886
                  · linarith only [h0, h4801, h4886, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h4888 | h4888
                    · linarith only [h0, h2, h4831, h4888, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h4890 | h4890
                      · linarith only [h0, h4825, h4890, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h4892 | h4892
                        · linarith only [h1, h2, h4831, h4892, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h4894 | h4894
                          · linarith only [h1, h4582, h4829, h4894, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h4896 | h4896
                            · linarith only [h1, h2, h4831, h4886, h4888, h4896, hc12, hc24, hlam, hphi]
                            · linarith only [h1, h2, h4886, h4896, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s1 m hb0 hb1 hb3 hb4 h0 h1

set_option maxHeartbeats 12618000 in
set_option maxHeartbeats 12618000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_I_s0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4899 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h4900 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4901 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h1, h4901, hlam]

end R2N4
