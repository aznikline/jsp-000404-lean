import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_6S5
import Jsp000404.R1LeavesN7_6S6
import Jsp000404.R1LeavesN7_6S7

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1027 | h1027
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1028 | h1028
    · linarith only [h1028, h4, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1030 | h1030
      · linarith only [h1027, h1030, h4, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1033 | h1033
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
            · linarith only [h0, h1034, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1036 | h1036
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                · linarith only [h1030, h1037, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1039 | h1039
                  · linarith only [h0, h1032, h1039, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h1036, h1039, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h1027, h1028, h1036, hc13, hc35, hlam, hphi]
          · linarith only [h1033, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h1032, h4, h6, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1045 | h1045
    · linarith only [h1027, h1045, h5, h6, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1047 | h1047
      · linarith only [h1047, h5, h6, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1050 | h1050
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1051 | h1051
            · linarith only [h0, h1051, h6, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1053 | h1053
              · linarith only [h1, h1027, h1053, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1055 | h1055
                · linarith only [h1047, h1055, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1057 | h1057
                  · linarith only [h1, h1027, h1049, h1057, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1059 | h1059
                    · linarith only [h0, h1045, h1050, h1057, h1059, h6, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1061 | h1061
                      · linarith only [h0, h1047, h1050, h1061, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1063 | h1063
                        · linarith only [h0, h1050, h1057, h1061, h1063, h6, hc23, hc34, hlam, hphi]
                        · rcases h0bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h0, h1050, h1057, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1065_1, u0elo0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            rcases p1065_3 (m.d 0 1) (by simp) with h1068 | h1068
                            · rcases p1065_3 (m.d 0 2) (by simp) with h1069 | h1069
                              · linarith only [h0, h1069, hlam]
                              · linarith only [h1069, h4, hlam]
                            · linarith only [h1, h1068, hlam]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            rcases p1065_3 (m.d 0 1) (by simp) with h1073 | h1073
                            · rcases p1065_3 (m.d 0 2) (by simp) with h1074 | h1074
                              · linarith only [h0, h1074, hlam]
                              · linarith only [h1074, h5, hlam]
                            · linarith only [h1073, h2, hlam]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1050, h1051, h1057, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1065_1, u0elo0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h0, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1059, h6, hc03, hc35, hlam, hphi, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1059, h1063, h6, hc04, hc45, hlam, hphi, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h6, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1, hlam, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h4, hlam, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1027, hlam, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1045, hlam, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h2, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h5, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1059, h1063, h5, h6, hc03, hc45, hlam, hphi, ht34, p1065_1]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h1047, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h3, hlam, p1065_0]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [h0, h1050, hc24, hlam, hphi, ht0b, ht45, ht5b, p1065_1, u0elo4]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            rcases p1065_3 (m.d 0 1) (by simp) with h1096 | h1096
                            · rcases p1065_3 (m.d 0 2) (by simp) with h1097 | h1097
                              · linarith only [h1097, h6, hlam]
                              · linarith only [h1097, h4, hlam]
                            · linarith only [h1, h1096, hlam]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            rcases p1065_3 (m.d 0 1) (by simp) with h1101 | h1101
                            · rcases p1065_3 (m.d 0 2) (by simp) with h1102 | h1102
                              · linarith only [h1102, h6, hlam]
                              · linarith only [h1102, h5, hlam]
                            · linarith only [h1101, h2, hlam]
                          · have p1065_0 := h1065c.1
                            have p1065_1 := h1065c.2.1
                            have p1065_2 := h1065c.2.2.1
                            have p1065_3 := h1065c.2.2.2
                            linarith only [hlam, p1065_0]
          · linarith only [h1050, h5, h6, hc12, hc25, hlam, hphi]
        · linarith only [h1049, h4, h6, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5 h6

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1109 | h1109
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1110 | h1110
    · linarith only [h1110, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1112 | h1112
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1113 | h1113
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1115 | h1115
            · linarith only [h0, h1115, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1117 | h1117
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1118 | h1118
                · linarith only [h1, h1110, h1118, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1120 | h1120
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1121 | h1121
                    · linarith only [h1110, h1114, h1115, h1121, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1123 | h1123
                      · linarith only [h1114, h1115, h1123, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1112, h1121, h1123, h4, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h1113, h1115, h1117, h1120, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
              · linarith only [h1109, h1114, h1117, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h1114, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1112, h1113, h4, h5, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
            · linarith only [h0, h1132, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1134 | h1134
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1135 | h1135
                · linarith only [h1, h1110, h1135, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1137 | h1137
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1138 | h1138
                    · linarith only [h0, h1110, h1131, h1138, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1140 | h1140
                      · linarith only [h1, h1112, h1131, h1140, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1142 | h1142
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1143 | h1143
                          · rcases h0bigk with h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c | h1144c
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1144_1, u0elo0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              rcases p1144_3 (m.d 0 1) (by simp) with h1147 | h1147
                              · rcases p1144_3 (m.d 0 2) (by simp) with h1148 | h1148
                                · linarith only [h0, h1148, hlam]
                                · linarith only [h1148, h4, hlam]
                              · linarith only [h1, h1147, hlam]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h0, h1134, h1140, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1144_1, u0elo0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              rcases p1144_3 (m.d 0 1) (by simp) with h1153 | h1153
                              · rcases p1144_3 (m.d 0 2) (by simp) with h1154 | h1154
                                · linarith only [h0, h1154, hlam]
                                · linarith only [h1109, h1154, hlam]
                              · linarith only [h1153, h3, hlam]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h0, hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1, h1131, h1138, h5, hc23, hc34, hlam, hphi, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h5, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1, h1112, h1131, h1138, h5, hc23, hc34, hlam, hphi, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h4, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1110, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1112, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h2, hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h0, h1134, h1140, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1144_1, u0elo3]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              rcases p1144_3 (m.d 0 1) (by simp) with h1170 | h1170
                              · rcases p1144_3 (m.d 0 2) (by simp) with h1171 | h1171
                                · linarith only [h1171, h5, hlam]
                                · linarith only [h1171, h4, hlam]
                              · linarith only [h1, h1170, hlam]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              rcases p1144_3 (m.d 0 1) (by simp) with h1176 | h1176
                              · rcases p1144_3 (m.d 0 2) (by simp) with h1177 | h1177
                                · linarith only [h1177, h5, hlam]
                                · linarith only [h1109, h1177, hlam]
                              · linarith only [h1176, h3, hlam]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h3, hlam, p1144_0]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1109, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1, h1109, h1131, h1138, h5, hc23, hc34, hlam, hphi, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [h1130, hlam, p1144_1]
                            · have p1144_0 := h1144c.1
                              have p1144_1 := h1144c.2.1
                              have p1144_2 := h1144c.2.2.1
                              have p1144_3 := h1144c.2.2.2
                              linarith only [hlam, p1144_0]
                          · linarith only [h0, h1134, h1138, h1142, h1143, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1142, h4, h5, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1130, h1132, h1134, h1137, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · linarith only [h1109, h1131, h1134, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · linarith only [h1131, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1109, h1130, h5, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1192 | h1192
    · linarith only [h1192, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1194 | h1194
      · linarith only [h1109, h1194, h4, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1196 | h1196
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1198 | h1198
            · linarith only [h0, h1198, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1200 | h1200
              · linarith only [h0, h1109, h1200, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1202 | h1202
                · linarith only [h0, h1192, h1197, h1202, h5, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1204 | h1204
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1205 | h1205
                    · linarith only [h0, h1192, h1197, h1205, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1207 | h1207
                      · linarith only [h1194, h1200, h1205, h1207, h3, h4, h5, hc12, hc34, hlam, hphi, ht23]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1209 | h1209
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1210 | h1210
                          · rcases h0bigk with h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c | h1211c
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u0elo0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              rcases p1211_3 (m.d 0 1) (by simp) with h1214 | h1214
                              · rcases p1211_3 (m.d 0 2) (by simp) with h1215 | h1215
                                · linarith only [h0, h1215, hlam]
                                · linarith only [h1215, h4, hlam]
                              · linarith only [h1, h1214, hlam]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1204, h2, hc45, hlam, hphi, ht0b, ht5b, p1211_1, u0elo0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h0, h1109, h1197, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u0elo0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h0, hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1, h1205, h5, hc13, hc34, hlam, hphi, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h5, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1109, hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h4, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1192, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1194, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h2, hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h0, h1197, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u0elo3]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              rcases p1211_3 (m.d 0 1) (by simp) with h1233 | h1233
                              · rcases p1211_3 (m.d 0 2) (by simp) with h1234 | h1234
                                · linarith only [h1234, h5, hlam]
                                · linarith only [h1234, h4, hlam]
                              · linarith only [h1, h1233, hlam]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h0, h1109, h1197, h2, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u0elo0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h3, hlam, p1211_0]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h0, h1197, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1211_1, u0elo4]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              rcases p1211_3 (m.d 0 1) (by simp) with h1242 | h1242
                              · rcases p1211_3 (m.d 0 2) (by simp) with h1243 | h1243
                                · linarith only [h1109, h1243, hlam]
                                · linarith only [h1243, h4, hlam]
                              · linarith only [h1, h1242, hlam]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [h1196, hlam, p1211_1]
                            · have p1211_0 := h1211c.1
                              have p1211_1 := h1211c.2.1
                              have p1211_2 := h1211c.2.2.1
                              have p1211_3 := h1211c.2.2.2
                              linarith only [hlam, p1211_0]
                          · linarith only [h0, h1197, h1205, h1210, h5, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1204, h1209, h2, h5, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1196, h1197, h1198, h1204, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h1197, h4, h5, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1253 | h1253
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1254 | h1254
            · linarith only [h0, h1254, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1256 | h1256
              · linarith only [h0, h1109, h1256, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1258 | h1258
                · linarith only [h1, h1192, h1258, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1260 | h1260
                  · linarith only [h1196, h1260, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1262 | h1262
                    · linarith only [h1192, h1253, h1254, h1260, h1262, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1264 | h1264
                      · linarith only [h1, h1194, h1253, h1264, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1266 | h1266
                        · linarith only [h1196, h1262, h1266, h4, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h1253, h1266, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1253, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  exact r1l7_20_12_14_M_LI_L_I_L_I_s4 m hb0 hb2 hb4 h0 h1 h2 h3 h4

set_option maxHeartbeats 9906000 in
set_option maxHeartbeats 9906000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s3 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
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
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x0 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3_x1 m hb0 hb2 hb4 hg0 hg1 hg2 hg3 h4

set_option maxHeartbeats 10200000 in
set_option maxHeartbeats 10200000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s2 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s3 m hb0 hb2 hb4 h0 h1 h2 h3
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4957 | h4957
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4958 | h4958
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4959 | h4959
        · linarith only [h0, h3, h4959, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4961 | h4961
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4962 | h4962
            · linarith only [h1, h3, h4962, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4964 | h4964
              · linarith only [h2, h3, h4964, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4966 | h4966
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4967 | h4967
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4968 | h4968
                    · linarith only [h0, h4959, h4968, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4970 | h4970
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4971 | h4971
                        · linarith only [h0, h2, h3, h4957, h4961, h4964, h4966, h4971, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h3, h4966, h4971, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h4961, h4962, h4970, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h4958, h4966, h4967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h4957, h4959, h4966, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4977 | h4977
            · linarith only [h1, h3, h4977, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4979 | h4979
              · linarith only [h0, h3, h4958, h4979, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4981 | h4981
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4982 | h4982
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4983 | h4983
                    · linarith only [h0, h4959, h4983, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4985 | h4985
                      · linarith only [h1, h4961, h4985, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h4987 | h4987
                        · linarith only [h2, h3, h4979, h4987, hlam]
                        · linarith only [h0, h3, h4981, h4987, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h4958, h4981, h4982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4957, h4959, h4981, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4992 | h4992
        · linarith only [h2, h3, h4958, h4992, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4994 | h4994
          · linarith only [h4957, h4958, h4994, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4996 | h4996
            · linarith only [h2, h3, h4957, h4958, h4996, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4998 | h4998
              · linarith only [h2, h3, h4998, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5000 | h5000
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5001 | h5001
                  · linarith only [h0, h4958, h5001, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5003 | h5003
                    · linarith only [h0, h3, h4992, h5003, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5005 | h5005
                      · linarith only [h2, h3, h4994, h5000, h5001, h5003, h5005, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5007 | h5007
                        · linarith only [h2, h3, h4998, h5003, h5007, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h2, h3, h5000, h5001, h5007, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h4957, h4958, h5000, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h5011 | h5011
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5012 | h5012
        · linarith only [h1, h3, h4957, h5012, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5014 | h5014
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5015 | h5015
            · linarith only [h1, h3, h5015, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5017 | h5017
              · linarith only [h1, h3, h4957, h5011, h5017, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5019 | h5019
                · linarith only [h0, h4957, h5019, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5021 | h5021
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5022 | h5022
                    · linarith only [h0, h3, h5012, h5022, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5024 | h5024
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5025 | h5025
                        · linarith only [h1, h3, h5017, h5019, h5021, h5022, h5025, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1, h3, h5019, h5021, h5025, hc24, hc45, hlam, hphi]
                      · linarith only [h1, h3, h5014, h5019, h5021, h5022, h5024, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h4957, h5011, h5021, hc12, hc23, hlam, hphi]
          · linarith only [h4957, h5011, h5014, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5031 | h5031
        · linarith only [h0, h3, h5031, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5033 | h5033
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5034 | h5034
            · linarith only [h1, h3, h5034, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5036 | h5036
              · linarith only [h2, h3, h5036, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5038 | h5038
                · linarith only [h0, h4957, h5038, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5040 | h5040
                  · linarith only [h0, h5011, h5040, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5042 | h5042
                    · linarith only [h0, h3, h5031, h5042, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5044 | h5044
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5045 | h5045
                        · linarith only [h1, h5011, h5036, h5044, h5045, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1, h3, h5044, h5045, hc34, hc45, hlam, hphi]
                      · linarith only [h5033, h5034, h5044, hc13, hc35, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5049 | h5049
            · linarith only [h1, h3, h5049, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h5051 | h5051
              · linarith only [h2, h3, h5051, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h5053 | h5053
                · linarith only [h0, h4957, h5053, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h5055 | h5055
                  · linarith only [h0, h5011, h5055, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h5057 | h5057
                    · linarith only [h0, h5031, h5057, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h5059 | h5059
                      · linarith only [h1, h5033, h5059, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h5061 | h5061
                        · linarith only [h2, h3, h5033, h5051, h5057, h5061, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h5063 | h5063
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5064 | h5064
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5065 | h5065
                              · linarith only [h0, h3, h5061, h5065, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5067 | h5067
                                · linarith only [h0, h5011, h5065, h5067, hc12, hc34, hlam, hphi, ht23]
                                · rcases h0bigk with h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c | h5069c
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h0, h3, h5057, hc12, hc25, hlam, hphi, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h1, h3, h5053, h5057, h5065, hc12, hc45, hlam, hphi, ht23, ht34, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h1, h3, h5033, h5053, h5057, h5065, hc12, hc45, hlam, hphi, ht23, ht34, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h3, hlam, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h0, hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h4957, hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5011, hlam, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5031, hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h1, hlam, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h0, h5033, h5063, hc12, hc24, hlam, hphi, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5033, hlam, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5049, hlam, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h2, hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h0, h2, h3, h5057, h5065, hc12, hc45, hlam, hphi, ht23, ht34, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h2, h3, h5057, h5065, hc03, hc45, hlam, hphi, ht34, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5051, hlam, p5069_0]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h5049, h5064, hc01, hc23, hlam, hphi, ht12, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h0, h5049, h5064, hc12, hc23, hlam, hphi, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h1, h5049, h5053, h5064, hc12, hc23, hlam, hphi, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [h2, h5049, h5053, h5059, h5064, hc12, hc23, hlam, hphi, p5069_1]
                                  · have p5069_0 := h5069c.1
                                    have p5069_1 := h5069c.2.1
                                    have p5069_2 := h5069c.2.2.1
                                    have p5069_3 := h5069c.2.2.2
                                    linarith only [hlam, p5069_0]
                            · linarith only [h1, h5033, h5053, h5063, h5064, hc12, hc35, hlam, hphi, ht23]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h5096 | h5096
                            · linarith only [h1, h5049, h5053, h5063, h5096, hc12, hc34, hlam, hphi, ht23]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h5098 | h5098
                              · linarith only [h2, h3, h5053, h5059, h5061, h5098, hc12, hc24, hlam, hphi]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h5100 | h5100
                                · linarith only [h0, h4957, h5063, h5098, h5100, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h0, h4957, h5063, h5100, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 10816000 in
set_option maxHeartbeats 10816000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_M_LI_L_I_L_I_s2 m hb0 hb2 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h5103 | h5103
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5104 | h5104
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5105 | h5105
        · linarith only [h0, h2, h5105, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5107 | h5107
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5108 | h5108
            · linarith only [h1, h2, h5108, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5110 | h5110
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5111 | h5111
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5112 | h5112
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5113 | h5113
                    · linarith only [h0, h5105, h5113, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5115 | h5115
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5116 | h5116
                        · linarith only [h0, h1, h2, h5108, h5112, h5116, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h2, h5112, h5116, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5107, h5112, h5113, h5115, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5104, h5105, h5112, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h5104, h5110, h5111, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5122 | h5122
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5123 | h5123
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5124 | h5124
                    · linarith only [h0, h5105, h5124, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5126 | h5126
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5127 | h5127
                        · linarith only [h1, h5108, h5127, hlam]
                        · linarith only [h0, h2, h5123, h5127, hc23, hc34, hlam, hphi]
                      · linarith only [h5107, h5123, h5126, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h5104, h5105, h5123, hc12, hc24, hlam, hphi]
                · linarith only [h2, h5103, h5122, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5133 | h5133
            · linarith only [h1, h2, h5133, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5135 | h5135
              · linarith only [h5104, h5107, h5135, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5137 | h5137
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5138 | h5138
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5139 | h5139
                    · linarith only [h0, h2, h5105, h5139, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5141 | h5141
                      · linarith only [h0, h5107, h5141, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5143 | h5143
                        · linarith only [h1, h2, h5103, h5104, h5133, h5138, h5141, h5143, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h2, h5103, h5138, h5141, h5143, hc23, hc34, hlam, hphi]
                  · linarith only [h5104, h5105, h5138, hc12, hc24, hlam, hphi]
                · linarith only [h2, h5103, h5137, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5148 | h5148
        · linarith only [h0, h2, h5148, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5150 | h5150
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5151 | h5151
            · linarith only [h1, h2, h5151, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5153 | h5153
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5154 | h5154
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5155 | h5155
                  · linarith only [h0, h5104, h5155, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5157 | h5157
                    · linarith only [h0, h2, h5148, h5157, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5159 | h5159
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5160 | h5160
                        · linarith only [h1, h2, h5104, h5151, h5157, h5160, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5162 | h5162
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5163 | h5163
                            · linarith only [h0, h2, h5159, h5160, h5163, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5165 | h5165
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5166 | h5166
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5167 | h5167
                                  · rcases h0bigk with h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c | h5168c
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, h2, h5104, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo3]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h2, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      rcases p5168_3 (m.d 0 1) (by simp) with h5173 | h5173
                                      · rcases p5168_3 (m.d 0 2) (by simp) with h5174 | h5174
                                        · linarith only [h0, h5174, hlam]
                                        · linarith only [h5150, h5174, hlam]
                                      · linarith only [h5103, h5173, hlam]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5104, hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5148, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5103, h5104, h5163, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h1, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo2]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5151, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      rcases p5168_3 (m.d 0 1) (by simp) with h5187 | h5187
                                      · rcases p5168_3 (m.d 0 2) (by simp) with h5188 | h5188
                                        · linarith only [h5104, h5188, hlam]
                                        · linarith only [h5150, h5188, hlam]
                                      · linarith only [h5103, h5187, hlam]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo3]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h0, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo3]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h1, h5155, h5159, h5165, h5167, hc45, hlam, hphi, ht0b, ht5b, p5168_1, u0elo3]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      rcases p5168_3 (m.d 0 1) (by simp) with h5196 | h5196
                                      · linarith only [h2, h5196, hlam]
                                      · linarith only [h5103, h5196, hlam]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5103, hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5150, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5153, hlam, p5168_0]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [h5154, hlam, p5168_1]
                                    · have p5168_0 := h5168c.1
                                      have p5168_1 := h5168c.2.1
                                      have p5168_2 := h5168c.2.2.1
                                      have p5168_3 := h5168c.2.2.2
                                      linarith only [hlam, p5168_0]
                                  · linarith only [h5104, h5163, h5167, hc02, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2, h5103, h5155, h5157, h5159, h5162, h5165, h5166, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                              · linarith only [h5104, h5153, h5165, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h2, h5155, h5159, h5162, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h1, h2, h5104, h5150, h5157, h5159, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h5104, h5150, h5154, hlam]
              · linarith only [h5104, h5150, h5153, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5211 | h5211
            · linarith only [h1, h2, h5211, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5213 | h5213
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5214 | h5214
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5215 | h5215
                  · linarith only [h0, h5104, h5215, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5217 | h5217
                    · linarith only [h0, h5148, h5217, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5219 | h5219
                      · linarith only [h0, h5150, h5219, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5221 | h5221
                        · linarith only [h1, h2, h5211, h5221, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5223 | h5223
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5224 | h5224
                            · linarith only [h0, h2, h5221, h5224, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5226 | h5226
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5227 | h5227
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5228 | h5228
                                  · rcases h0bigk with h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c | h5229c
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h2, h5217, hc02, hc24, hlam, hphi, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h2, h5217, h5224, hc03, hc34, hlam, hphi, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h2, hlam, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h2, h5150, h5217, h5224, hc02, hc34, hlam, hphi, ht23, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h0, hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5104, hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5148, hlam, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5150, hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h1, hlam, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h0, h1, h2, h5217, h5224, hc12, hc34, hlam, hphi, ht23, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5211, hlam, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h0, h1, h2, h5150, h5217, h5224, hc12, hc34, hlam, hphi, ht23, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h1, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5229_1, u0elo3]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      rcases p5229_3 (m.d 0 1) (by simp) with h5246 | h5246
                                      · linarith only [h2, h5246, hlam]
                                      · linarith only [h0, h5246, hlam]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5213, h5228, hc45, hlam, hphi, ht0b, ht5b, p5229_1, u0elo3]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      rcases p5229_3 (m.d 0 1) (by simp) with h5251 | h5251
                                      · linarith only [h2, h5251, hlam]
                                      · linarith only [h5103, h5251, hlam]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5103, hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h0, h2, h5103, h5217, h5224, hc12, hc34, hlam, hphi, ht23, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5213, hlam, p5229_0]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [h5214, hlam, p5229_1]
                                    · have p5229_0 := h5229c.1
                                      have p5229_1 := h5229c.2.1
                                      have p5229_2 := h5229c.2.2.1
                                      have p5229_3 := h5229c.2.2.2
                                      linarith only [hlam, p5229_0]
                                  · linarith only [h0, h2, h5217, h5224, h5228, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h2, h5103, h5217, h5223, h5227, hlam]
                              · linarith only [h1, h2, h5213, h5217, h5224, h5226, hc23, hc34, hlam, hphi]
                          · linarith only [h1, h2, h5215, h5223, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1, h2, h5213, h5214, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5264 | h5264
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5265 | h5265
                  · linarith only [h0, h5104, h5265, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5267 | h5267
                    · linarith only [h1, h2, h5148, h5265, h5267, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5269 | h5269
                      · linarith only [h0, h5150, h5269, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5271 | h5271
                        · linarith only [h1, h5211, h5271, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5273 | h5273
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5274 | h5274
                            · linarith only [h1, h2, h5265, h5271, h5274, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5276 | h5276
                              · linarith only [h1, h5213, h5265, h5274, h5276, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5278 | h5278
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5279 | h5279
                                  · rcases h0bigk with h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c | h5280c
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h0, h2, h5267, h5274, hc12, hc34, hlam, hphi, ht23, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h1, h2, h5265, h5267, h5274, hc12, hc34, hlam, hphi, ht23, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h2, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h1, h2, h5213, h5265, h5267, h5274, hc12, hc34, hlam, hphi, ht23, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h0, hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5104, hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5148, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5150, hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h1, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h0, h5104, h5276, h5279, hc12, hc34, hlam, hphi, ht23, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5211, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5213, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5103, hc15, hlam, hphi, ht0b, ht5b, p5280_1, u0elo3]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      rcases p5280_3 (m.d 0 1) (by simp) with h5297 | h5297
                                      · linarith only [h2, h5297, hlam]
                                      · linarith only [h0, h5297, hlam]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      rcases p5280_3 (m.d 0 1) (by simp) with h5300 | h5300
                                      · linarith only [h2, h5300, hlam]
                                      · linarith only [h1, h5300, hlam]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      rcases p5280_3 (m.d 0 1) (by simp) with h5304 | h5304
                                      · linarith only [h2, h5304, hlam]
                                      · linarith only [h5103, h5304, hlam]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5103, hlam, p5280_0]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h0, h2, h5103, h5267, h5274, hc12, hc34, hlam, hphi, ht23, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h2, h5103, h5267, h5274, hc03, hc34, hlam, hphi, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [h5264, hlam, p5280_1]
                                    · have p5280_0 := h5280c.1
                                      have p5280_1 := h5280c.2.1
                                      have p5280_2 := h5280c.2.2.1
                                      have p5280_3 := h5280c.2.2.2
                                      linarith only [hlam, p5280_0]
                                  · linarith only [h0, h2, h5267, h5274, h5279, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2, h5265, h5267, h5278, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h1, h2, h5264, h5265, h5273, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · linarith only [h2, h5103, h5264, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5316 | h5316
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5317 | h5317
        · linarith only [h0, h2, h5317, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5319 | h5319
          · linarith only [h0, h5103, h5319, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5321 | h5321
            · linarith only [h1, h2, h5321, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5323 | h5323
              · linarith only [h0, h5103, h5316, h5323, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5325 | h5325
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5326 | h5326
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5327 | h5327
                    · linarith only [h0, h5317, h5327, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5329 | h5329
                      · linarith only [h0, h5103, h5319, h5329, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5331 | h5331
                        · linarith only [h1, h2, h5321, h5325, h5327, h5331, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h2, h5326, h5331, hc23, hc34, hlam, hphi]
                  · linarith only [h5316, h5317, h5326, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5335 | h5335
                  · linarith only [h0, h2, h5325, h5335, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h5316, h5325, h5335, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5338 | h5338
        · linarith only [h1, h2, h5316, h5338, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5340 | h5340
          · linarith only [h1, h5103, h5316, h5340, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5342 | h5342
            · linarith only [h1, h2, h5342, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5344 | h5344
              · linarith only [h1, h5103, h5344, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5346 | h5346
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5347 | h5347
                  · linarith only [h0, h5316, h5347, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5349 | h5349
                    · linarith only [h0, h5103, h5338, h5346, h5349, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5351 | h5351
                      · linarith only [h1, h5340, h5347, h5351, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5353 | h5353
                        · linarith only [h1, h2, h5342, h5349, h5353, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5355 | h5355
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5356 | h5356
                            · linarith only [h0, h5103, h5353, h5355, h5356, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5358 | h5358
                              · linarith only [h0, h5316, h5344, h5356, h5358, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5360 | h5360
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5361 | h5361
                                  · rcases h0bigk with h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c | h5362c
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h0, h5103, h5349, h5355, hc12, hc24, hlam, hphi, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h0, h5103, h5316, h5349, h5355, hc12, hc24, hlam, hphi, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h2, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5103, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h0, hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5316, hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5338, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5340, hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h1, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h0, h1, h5103, h5349, h5355, hc12, hc24, hlam, hphi, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5342, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5344, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5362_1, u0elo3]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      rcases p5362_3 (m.d 0 1) (by simp) with h5379 | h5379
                                      · linarith only [h2, h5379, hlam]
                                      · linarith only [h0, h5379, hlam]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      rcases p5362_3 (m.d 0 1) (by simp) with h5382 | h5382
                                      · linarith only [h2, h5382, hlam]
                                      · linarith only [h1, h5382, hlam]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [hlam, p5362_0]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h1, h5103, h5347, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5362_1, u0elo3]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h1, h5347, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5362_1, u0elo4]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      rcases p5362_3 (m.d 0 1) (by simp) with h5388 | h5388
                                      · linarith only [h5103, h5388, hlam]
                                      · linarith only [h0, h5388, hlam]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      rcases p5362_3 (m.d 0 1) (by simp) with h5391 | h5391
                                      · linarith only [h5103, h5391, hlam]
                                      · linarith only [h1, h5391, hlam]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [h5346, hlam, p5362_1]
                                    · have p5362_0 := h5362c.1
                                      have p5362_1 := h5362c.2.1
                                      have p5362_2 := h5362c.2.2.1
                                      have p5362_3 := h5362c.2.2.2
                                      linarith only [hlam, p5362_0]
                                  · linarith only [h1, h2, h5346, h5347, h5349, h5356, h5361, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h2, h5346, h5349, h5360, hlam]
                          · linarith only [h2, h5346, h5355, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5399 | h5399
                  · linarith only [h0, h5316, h5399, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5401 | h5401
                    · linarith only [h0, h2, h5346, h5401, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5403 | h5403
                      · linarith only [h0, h5340, h5403, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5405 | h5405
                        · linarith only [h1, h2, h5342, h5405, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5407 | h5407
                          · linarith only [h1, h2, h5346, h5399, h5401, h5407, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h2, h5399, h5407, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  exact r1l7_20_12_14_M_LI_L_I_L_I_s1 m hb0 hb2 hb4 h0 h1

set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5412 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  linarith only [h0, h1, h5412, hlam]

end R2N4
