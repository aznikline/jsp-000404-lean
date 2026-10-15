import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h4106 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 0 3 5 (by decide) (by decide) with h5969 | h5969
  · rcases m.htr 0 4 5 (by decide) (by decide) with h5970 | h5970
    · rcases m.htr 1 2 3 (by decide) (by decide) with h5971 | h5971
      · linarith only [h0, h4, h5969, h5971, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h5973 | h5973
        · linarith only [h0, h3476, h5973, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h5975 | h5975
          · linarith only [h0, h4023, h5975, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5977 | h5977
            · linarith only [h1, h4106, h5977, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h5979 | h5979
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5980 | h5980
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5981 | h5981
                  · linarith only [h4106, h5969, h5981, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5983 | h5983
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5984 | h5984
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5985 | h5985
                        · rcases h0bigk with h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c | h5986c
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            rcases p5986_3 (m.d 0 1) (by simp) with h5988 | h5988
                            · rcases p5986_3 (m.d 0 2) (by simp) with h5989 | h5989
                              · linarith only [h0, h5989, hlam]
                              · rcases p5986_3 (m.d 0 3) (by simp) with h5991 | h5991
                                · linarith only [h1, h5991, hlam]
                                · linarith only [h4, h5991, hlam]
                            · linarith only [h0, h5988, hlam]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h1, h5979, h5985, hc01, hlam, hphi, ht0b, ht5b, p5986_1, u5ehi4]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h1, h4106, h5979, h5985, hc01, hlam, hphi, ht0b, ht5b, p5986_1, u5ehi4]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            rcases p5986_3 (m.d 0 1) (by simp) with h5997 | h5997
                            · rcases p5986_3 (m.d 0 2) (by simp) with h5998 | h5998
                              · linarith only [h0, h5998, hlam]
                              · rcases p5986_3 (m.d 0 3) (by simp) with h6000 | h6000
                                · linarith only [h1, h6000, hlam]
                                · linarith only [h5969, h6000, hlam]
                            · linarith only [h3, h5997, hlam]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h0, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h4, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h3476, hlam, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h4023, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h1, hlam, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h4, h5981, hc02, hc34, hlam, hphi, ht23, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h4106, hlam, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h3, h4, h5981, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5986_1, u5ehi1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h2, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            rcases p5986_3 (m.d 0 1) (by simp) with h6015 | h6015
                            · rcases p5986_3 (m.d 0 2) (by simp) with h6016 | h6016
                              · linarith only [h3476, h6016, hlam]
                              · rcases p5986_3 (m.d 0 3) (by simp) with h6018 | h6018
                                · linarith only [h4106, h6018, hlam]
                                · linarith only [h4, h6018, hlam]
                            · linarith only [h0, h6015, hlam]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h1, h5979, hc04, hlam, hphi, ht0b, ht5b, p5986_1, u5ehi3]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            rcases p5986_3 (m.d 0 1) (by simp) with h6024 | h6024
                            · rcases p5986_3 (m.d 0 2) (by simp) with h6025 | h6025
                              · linarith only [h3476, h6025, hlam]
                              · rcases p5986_3 (m.d 0 3) (by simp) with h6027 | h6027
                                · linarith only [h4106, h6027, hlam]
                                · linarith only [h5969, h6027, hlam]
                            · linarith only [h3, h6024, hlam]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h3, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h0, h4023, h5981, h5983, hc12, hc34, hlam, hphi, ht23, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h5969, hlam, p5986_0]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [h5970, hlam, p5986_1]
                          · have p5986_0 := h5986c.1
                            have p5986_1 := h5986c.2.1
                            have p5986_2 := h5986c.2.2.1
                            have p5986_3 := h5986c.2.2.2
                            linarith only [hlam, p5986_0]
                        · linarith only [h0, h4, h5981, h5985, hc12, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h3476, h5970, h5984, hlam]
                    · linarith only [h1, h4, h5979, h5983, hlam]
                · linarith only [h5970, h5977, h5979, h5980, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
              · linarith only [h4106, h5969, h5979, hc13, hc34, hlam, hphi]
    · linarith only [h4106, h5969, h5970, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6042 | h6042
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6043 | h6043
      · linarith only [h0, h4, h6043, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6045 | h6045
        · linarith only [h0, h3476, h6045, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6047 | h6047
          · linarith only [h0, h4023, h6047, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6049 | h6049
            · linarith only [h1, h4106, h6049, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6051 | h6051
              · linarith only [h1, h5969, h6051, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6053 | h6053
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6054 | h6054
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6055 | h6055
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6056 | h6056
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6057 | h6057
                        · rcases h0bigk with h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c | h6058c
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            rcases p6058_3 (m.d 0 1) (by simp) with h6060 | h6060
                            · rcases p6058_3 (m.d 0 2) (by simp) with h6061 | h6061
                              · linarith only [h0, h6061, hlam]
                              · rcases p6058_3 (m.d 0 3) (by simp) with h6063 | h6063
                                · linarith only [h1, h6063, hlam]
                                · linarith only [h4, h6063, hlam]
                            · linarith only [h0, h6060, hlam]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            rcases p6058_3 (m.d 0 1) (by simp) with h6067 | h6067
                            · rcases p6058_3 (m.d 0 2) (by simp) with h6068 | h6068
                              · linarith only [h0, h6068, hlam]
                              · rcases p6058_3 (m.d 0 3) (by simp) with h6070 | h6070
                                · linarith only [h1, h6070, hlam]
                                · rcases p6058_3 (m.d 0 4) (by simp) with h6072 | h6072
                                  · linarith only [h2, h6072, hlam]
                                  · linarith only [h4106, h6072, hlam]
                            · linarith only [h1, h6067, hlam]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h2, h6053, hc01, hlam, hphi, ht0b, ht5b, p6058_1, u5ehi4]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            rcases p6058_3 (m.d 0 1) (by simp) with h6077 | h6077
                            · rcases p6058_3 (m.d 0 2) (by simp) with h6078 | h6078
                              · linarith only [h0, h6078, hlam]
                              · rcases p6058_3 (m.d 0 3) (by simp) with h6080 | h6080
                                · linarith only [h1, h6080, hlam]
                                · rcases p6058_3 (m.d 0 4) (by simp) with h6082 | h6082
                                  · linarith only [h2, h6082, hlam]
                                  · linarith only [h6042, h6082, hlam]
                            · linarith only [h3, h6077, hlam]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h0, hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h4, hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h3476, hlam, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h4023, hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h1, hlam, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h5969, h6054, h6057, hc02, hc23, hlam, hphi, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h4106, hlam, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h5969, hlam, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h2, hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h0, h4106, h6054, hc12, hc23, hlam, hphi, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h0, h4, h4106, h6054, hc12, hc23, hlam, hphi, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h4106, h6054, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6058_1, u5ehi0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h3, hlam, p6058_0]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h0, h5969, h6054, h6057, hc12, hc23, hlam, hphi, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h0, h4, h5969, h6054, h6057, hc12, hc23, hlam, hphi, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [h6042, hlam, p6058_1]
                          · have p6058_0 := h6058c.1
                            have p6058_1 := h6058c.2.1
                            have p6058_2 := h6058c.2.2.1
                            have p6058_3 := h6058c.2.2.2
                            linarith only [hlam, p6058_0]
                        · linarith only [h2, h4106, h6053, h6057, hlam]
                      · linarith only [h0, h2, h3476, h4106, h6053, h6056, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h2, h4106, h6053, h6054, h6055, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6109 | h6109
                    · linarith only [h0, h4, h5969, h6054, h6109, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6111 | h6111
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6112 | h6112
                        · rcases h0bigk with h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c | h6113c
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6115 | h6115
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6116 | h6116
                              · linarith only [h0, h6116, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6118 | h6118
                                · linarith only [h1, h6118, hlam]
                                · linarith only [h4, h6118, hlam]
                            · linarith only [h0, h6115, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6122 | h6122
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6123 | h6123
                              · linarith only [h0, h6123, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6125 | h6125
                                · linarith only [h1, h6125, hlam]
                                · rcases p6113_3 (m.d 0 4) (by simp) with h6127 | h6127
                                  · linarith only [h2, h6127, hlam]
                                  · linarith only [h4106, h6127, hlam]
                            · linarith only [h1, h6122, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h2, h6053, hc01, hlam, hphi, ht0b, ht5b, p6113_1, u5ehi4]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6132 | h6132
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6133 | h6133
                              · linarith only [h0, h6133, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6135 | h6135
                                · linarith only [h1, h6135, hlam]
                                · rcases p6113_3 (m.d 0 4) (by simp) with h6137 | h6137
                                  · linarith only [h2, h6137, hlam]
                                  · linarith only [h6042, h6137, hlam]
                            · linarith only [h3, h6132, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h0, hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h4, hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h3476, hlam, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h4023, hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h1, hlam, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h0, h4, h6109, h6112, hc12, hc34, hlam, hphi, ht23, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h4106, hlam, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h5969, hlam, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h2, hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6152 | h6152
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6153 | h6153
                              · linarith only [h3476, h6153, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6155 | h6155
                                · linarith only [h4106, h6155, hlam]
                                · linarith only [h4, h6155, hlam]
                            · linarith only [h0, h6152, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6159 | h6159
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6160 | h6160
                              · linarith only [h3476, h6160, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6162 | h6162
                                · linarith only [h4106, h6162, hlam]
                                · rcases p6113_3 (m.d 0 4) (by simp) with h6164 | h6164
                                  · rcases p6113_3 (m.d 0 5) (by simp) with h6165 | h6165
                                    · linarith only [h6042, h6165, hlam]
                                    · linarith only [h5969, h6165, hlam]
                                  · linarith only [h4106, h6164, hlam]
                            · linarith only [h1, h6159, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6171 | h6171
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6172 | h6172
                              · linarith only [h3476, h6172, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6174 | h6174
                                · linarith only [h4106, h6174, hlam]
                                · rcases p6113_3 (m.d 0 4) (by simp) with h6176 | h6176
                                  · rcases p6113_3 (m.d 0 5) (by simp) with h6177 | h6177
                                    · linarith only [h6042, h6177, hlam]
                                    · rcases h2bigk with h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c | h6179c
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h4, h6109, h6112, hc12, hc34, hlam, hphi, ht23, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h4, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h3476, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h4023, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h0, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6043, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6045, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6047, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6109, h6112, hc02, hc34, hlam, hphi, ht23, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6109, h6112, hc12, hc34, hlam, hphi, ht23, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6054, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6109, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        rcases p6179_3 (m.d 0 2) (by simp) with h6195 | h6195
                                        · linarith only [h6195, hlam, p6179_0]
                                        · rcases p6179_3 (m.d 1 2) (by simp) with h6197 | h6197
                                          · linarith only [h6045, h6197, hlam]
                                          · rcases p6179_3 (m.d 2 3) (by simp) with h6199 | h6199
                                            · linarith only [h6054, h6199, hlam]
                                            · linarith only [h4, h6199, hlam]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        rcases p6179_3 (m.d 0 2) (by simp) with h6202 | h6202
                                        · linarith only [h3476, h6202, hlam]
                                        · linarith only [h0, h6202, hlam]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h0, h4, hc12, hc24, hlam, hphi, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h0, h4, h6054, h6109, hc12, hc34, hlam, hphi, ht23, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        rcases p6179_3 (m.d 0 2) (by simp) with h6208 | h6208
                                        · linarith only [h6208, hlam, p6179_0]
                                        · rcases p6179_3 (m.d 1 2) (by simp) with h6210 | h6210
                                          · linarith only [h6047, h6210, hlam]
                                          · rcases p6179_3 (m.d 2 3) (by simp) with h6212 | h6212
                                            · linarith only [h6109, h6212, hlam]
                                            · linarith only [h4, h6212, hlam]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        rcases p6179_3 (m.d 0 2) (by simp) with h6215 | h6215
                                        · linarith only [h4023, h6215, hlam]
                                        · linarith only [h0, h6215, hlam]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p6179_1]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [h6111, hlam, p6179_0]
                                      · have p6179_0 := h6179c.1
                                        have p6179_1 := h6179c.2.1
                                        have p6179_2 := h6179c.2.2.1
                                        have p6179_3 := h6179c.2.2.2
                                        linarith only [hlam, p6179_0]
                                  · linarith only [h6042, h6176, hlam]
                            · linarith only [h3, h6171, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h3, hlam, p6113_0]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6224 | h6224
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6225 | h6225
                              · linarith only [h4023, h6225, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6227 | h6227
                                · linarith only [h5969, h6227, hlam]
                                · linarith only [h4, h6227, hlam]
                            · linarith only [h0, h6224, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            rcases p6113_3 (m.d 0 1) (by simp) with h6231 | h6231
                            · rcases p6113_3 (m.d 0 2) (by simp) with h6232 | h6232
                              · linarith only [h4023, h6232, hlam]
                              · rcases p6113_3 (m.d 0 3) (by simp) with h6234 | h6234
                                · linarith only [h5969, h6234, hlam]
                                · rcases p6113_3 (m.d 0 4) (by simp) with h6236 | h6236
                                  · rcases p6113_3 (m.d 0 5) (by simp) with h6237 | h6237
                                    · rcases h2bigk with h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c | h6238c
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6113_1, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h4, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h3476, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h4023, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h0, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6043, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6045, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6047, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h0, h6054, hc12, hc34, hlam, hphi, ht23, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6054, hc12, hc34, hlam, hphi, ht23, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6054, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6109, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        rcases p6238_3 (m.d 0 2) (by simp) with h6254 | h6254
                                        · linarith only [h6254, hlam, p6238_0]
                                        · rcases p6238_3 (m.d 1 2) (by simp) with h6256 | h6256
                                          · linarith only [h6045, h6256, hlam]
                                          · rcases p6238_3 (m.d 2 3) (by simp) with h6258 | h6258
                                            · linarith only [h6054, h6258, hlam]
                                            · linarith only [h4, h6258, hlam]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        rcases p6238_3 (m.d 0 2) (by simp) with h6261 | h6261
                                        · linarith only [h3476, h6261, hlam]
                                        · linarith only [h0, h6261, hlam]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h0, h4, h6054, hc12, hc34, hlam, hphi, ht23, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h4023, h6054, hc03, hc34, hlam, hphi, p6113_1, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        rcases p6238_3 (m.d 0 2) (by simp) with h6267 | h6267
                                        · linarith only [h6267, hlam, p6238_0]
                                        · rcases p6238_3 (m.d 1 2) (by simp) with h6269 | h6269
                                          · linarith only [h6047, h6269, hlam]
                                          · rcases p6238_3 (m.d 2 3) (by simp) with h6271 | h6271
                                            · linarith only [h6109, h6271, hlam]
                                            · linarith only [h4, h6271, hlam]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        rcases p6238_3 (m.d 0 2) (by simp) with h6274 | h6274
                                        · linarith only [h4023, h6274, hlam]
                                        · linarith only [h0, h6274, hlam]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p6238_1]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [h6111, hlam, p6238_0]
                                      · have p6238_0 := h6238c.1
                                        have p6238_1 := h6238c.2.1
                                        have p6238_2 := h6238c.2.2.1
                                        have p6238_3 := h6238c.2.2.2
                                        linarith only [hlam, p6238_0]
                                    · linarith only [h5969, h6237, hlam]
                                  · linarith only [h4106, h6236, hlam]
                            · linarith only [h1, h6231, hlam]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [h6042, hlam, p6113_1]
                          · have p6113_0 := h6113c.1
                            have p6113_1 := h6113c.2.1
                            have p6113_2 := h6113c.2.2.1
                            have p6113_3 := h6113c.2.2.2
                            linarith only [hlam, p6113_0]
                        · linarith only [h2, h3476, h6053, h6054, h6112, hlam]
                      · linarith only [h3, h3476, h6042, h6053, h6111, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6287 | h6287
                  · linarith only [h4106, h6042, h6043, h6049, h6053, h6287, hc12, hc23, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6289 | h6289
                    · linarith only [h1, h5969, h6043, h6287, h6289, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6291 | h6291
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6292 | h6292
                        · rcases h0bigk with h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c | h6293c
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6295 | h6295
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6296 | h6296
                              · linarith only [h0, h6296, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6298 | h6298
                                · linarith only [h1, h6298, hlam]
                                · linarith only [h4, h6298, hlam]
                            · linarith only [h0, h6295, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6302 | h6302
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6303 | h6303
                              · linarith only [h0, h6303, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6305 | h6305
                                · linarith only [h1, h6305, hlam]
                                · rcases p6293_3 (m.d 0 4) (by simp) with h6307 | h6307
                                  · linarith only [h2, h6307, hlam]
                                  · linarith only [h4106, h6307, hlam]
                            · linarith only [h1, h6302, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h6042, h6043, h6049, h6053, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6312 | h6312
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6313 | h6313
                              · linarith only [h0, h6313, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6315 | h6315
                                · linarith only [h1, h6315, hlam]
                                · rcases p6293_3 (m.d 0 4) (by simp) with h6317 | h6317
                                  · linarith only [h2, h6317, hlam]
                                  · linarith only [h6042, h6317, hlam]
                            · linarith only [h3, h6312, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h0, hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h4, hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h3476, hlam, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h4023, hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h1, hlam, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h4, h6289, h6292, hc02, hc34, hlam, hphi, ht23, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h4106, hlam, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h5969, hlam, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h2, hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6332 | h6332
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6333 | h6333
                              · linarith only [h3476, h6333, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6335 | h6335
                                · linarith only [h4106, h6335, hlam]
                                · linarith only [h4, h6335, hlam]
                            · linarith only [h0, h6332, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6339 | h6339
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6340 | h6340
                              · linarith only [h3476, h6340, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6342 | h6342
                                · linarith only [h4106, h6342, hlam]
                                · rcases p6293_3 (m.d 0 4) (by simp) with h6344 | h6344
                                  · rcases p6293_3 (m.d 0 5) (by simp) with h6345 | h6345
                                    · linarith only [h6042, h6345, hlam]
                                    · linarith only [h5969, h6345, hlam]
                                  · linarith only [h4106, h6344, hlam]
                            · linarith only [h1, h6339, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h3476, h6042, h6043, h6049, h6053, hc12, hc24, hlam, hphi, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h3, hlam, p6293_0]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6353 | h6353
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6354 | h6354
                              · linarith only [h4023, h6354, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6356 | h6356
                                · linarith only [h5969, h6356, hlam]
                                · linarith only [h4, h6356, hlam]
                            · linarith only [h0, h6353, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            rcases p6293_3 (m.d 0 1) (by simp) with h6360 | h6360
                            · rcases p6293_3 (m.d 0 2) (by simp) with h6361 | h6361
                              · linarith only [h4023, h6361, hlam]
                              · rcases p6293_3 (m.d 0 3) (by simp) with h6363 | h6363
                                · linarith only [h5969, h6363, hlam]
                                · rcases p6293_3 (m.d 0 4) (by simp) with h6365 | h6365
                                  · rcases p6293_3 (m.d 0 5) (by simp) with h6366 | h6366
                                    · rcases h2bigk with h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c | h6367c
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h4, h6289, h6292, hc12, hc34, hlam, hphi, ht23, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h4, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h3476, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h4023, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h0, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6043, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6045, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6047, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6289, h6292, hc02, hc34, hlam, hphi, ht23, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6289, h6292, hc12, hc34, hlam, hphi, ht23, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6287, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6289, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        rcases p6367_3 (m.d 0 2) (by simp) with h6383 | h6383
                                        · linarith only [h6383, hlam, p6367_0]
                                        · rcases p6367_3 (m.d 1 2) (by simp) with h6385 | h6385
                                          · linarith only [h6045, h6385, hlam]
                                          · rcases p6367_3 (m.d 2 3) (by simp) with h6387 | h6387
                                            · linarith only [h6287, h6387, hlam]
                                            · linarith only [h4, h6387, hlam]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        rcases p6367_3 (m.d 0 2) (by simp) with h6390 | h6390
                                        · linarith only [h3476, h6390, hlam]
                                        · linarith only [h0, h6390, hlam]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h0, h4, h6287, hc12, hc34, hlam, hphi, ht23, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h4023, h6287, hc03, hc34, hlam, hphi, p6293_1, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        rcases p6367_3 (m.d 0 2) (by simp) with h6396 | h6396
                                        · linarith only [h6396, hlam, p6367_0]
                                        · rcases p6367_3 (m.d 1 2) (by simp) with h6398 | h6398
                                          · linarith only [h6047, h6398, hlam]
                                          · rcases p6367_3 (m.d 2 3) (by simp) with h6400 | h6400
                                            · linarith only [h6289, h6400, hlam]
                                            · linarith only [h4, h6400, hlam]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        rcases p6367_3 (m.d 0 2) (by simp) with h6403 | h6403
                                        · linarith only [h4023, h6403, hlam]
                                        · linarith only [h0, h6403, hlam]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p6367_1]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [h6291, hlam, p6367_0]
                                      · have p6367_0 := h6367c.1
                                        have p6367_1 := h6367c.2.1
                                        have p6367_2 := h6367c.2.2.1
                                        have p6367_3 := h6367c.2.2.2
                                        linarith only [hlam, p6367_0]
                                    · linarith only [h5969, h6366, hlam]
                                  · linarith only [h4106, h6365, hlam]
                            · linarith only [h1, h6360, hlam]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [h6042, hlam, p6293_1]
                          · have p6293_0 := h6293c.1
                            have p6293_1 := h6293c.2.1
                            have p6293_2 := h6293c.2.2.1
                            have p6293_3 := h6293c.2.2.2
                            linarith only [hlam, p6293_0]
                        · linarith only [h3476, h6042, h6287, h6292, hlam]
                      · linarith only [h3476, h6042, h6291, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6416 | h6416
      · linarith only [h0, h4, h6416, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6418 | h6418
        · linarith only [h0, h3476, h6418, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6420 | h6420
          · linarith only [h0, h4023, h6420, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6422 | h6422
            · linarith only [h1, h4106, h6422, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6424 | h6424
              · linarith only [h1, h5969, h6424, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6426 | h6426
                · linarith only [h2, h6042, h6426, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6428 | h6428
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6429 | h6429
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6430 | h6430
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6431 | h6431
                        · linarith only [h0, h3476, h6042, h6428, h6431, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h4, h4106, h6428, h6430, h6431, hc12, hc23, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6434 | h6434
                        · linarith only [h0, h3476, h6430, h6434, hc12, hc34, hlam, hphi, ht23]
                        · rcases h0bigk with h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c | h6436c
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            rcases p6436_3 (m.d 0 1) (by simp) with h6438 | h6438
                            · rcases p6436_3 (m.d 0 2) (by simp) with h6439 | h6439
                              · linarith only [h0, h6439, hlam]
                              · rcases p6436_3 (m.d 0 3) (by simp) with h6441 | h6441
                                · linarith only [h1, h6441, hlam]
                                · linarith only [h4, h6441, hlam]
                            · linarith only [h0, h6438, hlam]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            rcases p6436_3 (m.d 0 1) (by simp) with h6445 | h6445
                            · rcases p6436_3 (m.d 0 2) (by simp) with h6446 | h6446
                              · linarith only [h0, h6446, hlam]
                              · rcases p6436_3 (m.d 0 3) (by simp) with h6448 | h6448
                                · linarith only [h1, h6448, hlam]
                                · rcases p6436_3 (m.d 0 4) (by simp) with h6450 | h6450
                                  · linarith only [h2, h6450, hlam]
                                  · linarith only [h4106, h6450, hlam]
                            · linarith only [h1, h6445, hlam]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            rcases p6436_3 (m.d 0 1) (by simp) with h6454 | h6454
                            · rcases p6436_3 (m.d 0 2) (by simp) with h6455 | h6455
                              · linarith only [h0, h6455, hlam]
                              · rcases p6436_3 (m.d 0 3) (by simp) with h6457 | h6457
                                · linarith only [h1, h6457, hlam]
                                · rcases p6436_3 (m.d 0 4) (by simp) with h6459 | h6459
                                  · linarith only [h2, h6459, hlam]
                                  · rcases p6436_3 (m.d 0 5) (by simp) with h6461 | h6461
                                    · linarith only [h3, h6461, hlam]
                                    · linarith only [h6042, h6461, hlam]
                            · linarith only [h2, h6454, hlam]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            rcases p6436_3 (m.d 0 1) (by simp) with h6465 | h6465
                            · rcases p6436_3 (m.d 0 2) (by simp) with h6466 | h6466
                              · linarith only [h0, h6466, hlam]
                              · rcases p6436_3 (m.d 0 3) (by simp) with h6468 | h6468
                                · linarith only [h1, h6468, hlam]
                                · rcases p6436_3 (m.d 0 4) (by simp) with h6470 | h6470
                                  · linarith only [h2, h6470, hlam]
                                  · rcases p6436_3 (m.d 0 5) (by simp) with h6472 | h6472
                                    · linarith only [h3, h6472, hlam]
                                    · rcases h2bigk with h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c | h6474c
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h4, h4106, h6428, hc12, hc24, hlam, hphi, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h4, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h3476, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h4023, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h0, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6416, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6418, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6420, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        rcases p6474_3 (m.d 0 2) (by simp) with h6485 | h6485
                                        · linarith only [h6485, hlam, p6474_0]
                                        · rcases p6474_3 (m.d 1 2) (by simp) with h6487 | h6487
                                          · linarith only [h6416, h6487, hlam]
                                          · rcases p6474_3 (m.d 2 3) (by simp) with h6489 | h6489
                                            · rcases p6474_3 (m.d 2 4) (by simp) with h6490 | h6490
                                              · linarith only [h6428, h6490, hlam]
                                              · linarith only [h3476, h6490, hlam]
                                            · linarith only [h6489, hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        rcases p6474_3 (m.d 0 2) (by simp) with h6494 | h6494
                                        · linarith only [h4, h6494, hlam]
                                        · linarith only [h0, h6494, hlam]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h3476, hc02, hc23, hlam, hphi, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h0, h4023, hc12, hc23, hlam, hphi, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h0, h6430, hc12, hc45, hlam, hphi, ht23, ht34, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6430, hc12, hc45, hlam, hphi, ht23, ht34, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6428, hlam, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [hlam, p6474_0]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6430, hlam, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        rcases p6474_3 (m.d 0 2) (by simp) with h6505 | h6505
                                        · linarith only [h6505, hlam, p6474_0]
                                        · rcases p6474_3 (m.d 1 2) (by simp) with h6507 | h6507
                                          · linarith only [h6420, h6507, hlam]
                                          · rcases p6474_3 (m.d 2 3) (by simp) with h6509 | h6509
                                            · rcases p6474_3 (m.d 2 4) (by simp) with h6510 | h6510
                                              · linarith only [h6430, h6510, hlam]
                                              · linarith only [h3476, h6510, hlam]
                                            · linarith only [h4, h6509, hlam]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        rcases p6474_3 (m.d 0 2) (by simp) with h6514 | h6514
                                        · linarith only [h4023, h6514, hlam]
                                        · linarith only [h0, h6514, hlam]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h6429, hlam, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [h0, h3476, hc12, hc25, hlam, hphi, p6474_1]
                                      · have p6474_0 := h6474c.1
                                        have p6474_1 := h6474c.2.1
                                        have p6474_2 := h6474c.2.2.1
                                        have p6474_3 := h6474c.2.2.2
                                        linarith only [hlam, p6474_0]
                            · linarith only [h3, h6465, hlam]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h0, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h4, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h3476, hlam, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h4023, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h1, hlam, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h0, h4106, hc12, hc34, hlam, hphi, ht23, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h4106, hlam, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h5969, hlam, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h2, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h0, h6042, hc12, hc45, hlam, hphi, ht23, ht34, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h1, h6042, h6416, hc12, hc45, hlam, hphi, ht23, ht34, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h6042, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h3, hlam, p6436_0]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h0, h5969, h6429, hc12, hc23, hlam, hphi, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h1, h5969, h6416, h6429, hc12, hc23, hlam, hphi, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [h2, h5969, h6416, h6422, h6429, hc12, hc23, hlam, hphi, p6436_1]
                          · have p6436_0 := h6436c.1
                            have p6436_1 := h6436c.2.1
                            have p6436_2 := h6436c.2.2.1
                            have p6436_3 := h6436c.2.2.2
                            linarith only [hlam, p6436_0]
                    · linarith only [h1, h4106, h6416, h6428, h6429, hc12, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6542 | h6542
                    · linarith only [h1, h5969, h6416, h6428, h6542, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6544 | h6544
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6545 | h6545
                        · rcases h0bigk with h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c | h6546c
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            rcases p6546_3 (m.d 0 1) (by simp) with h6548 | h6548
                            · rcases p6546_3 (m.d 0 2) (by simp) with h6549 | h6549
                              · linarith only [h0, h6549, hlam]
                              · rcases p6546_3 (m.d 0 3) (by simp) with h6551 | h6551
                                · linarith only [h1, h6551, hlam]
                                · linarith only [h4, h6551, hlam]
                            · linarith only [h0, h6548, hlam]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            rcases p6546_3 (m.d 0 1) (by simp) with h6555 | h6555
                            · rcases p6546_3 (m.d 0 2) (by simp) with h6556 | h6556
                              · linarith only [h0, h6556, hlam]
                              · rcases p6546_3 (m.d 0 3) (by simp) with h6558 | h6558
                                · linarith only [h1, h6558, hlam]
                                · rcases p6546_3 (m.d 0 4) (by simp) with h6560 | h6560
                                  · linarith only [h2, h6560, hlam]
                                  · linarith only [h4106, h6560, hlam]
                            · linarith only [h1, h6555, hlam]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            rcases p6546_3 (m.d 0 1) (by simp) with h6564 | h6564
                            · rcases p6546_3 (m.d 0 2) (by simp) with h6565 | h6565
                              · linarith only [h0, h6565, hlam]
                              · rcases p6546_3 (m.d 0 3) (by simp) with h6567 | h6567
                                · linarith only [h1, h6567, hlam]
                                · rcases p6546_3 (m.d 0 4) (by simp) with h6569 | h6569
                                  · linarith only [h2, h6569, hlam]
                                  · rcases p6546_3 (m.d 0 5) (by simp) with h6571 | h6571
                                    · linarith only [h3, h6571, hlam]
                                    · linarith only [h6042, h6571, hlam]
                            · linarith only [h2, h6564, hlam]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            rcases p6546_3 (m.d 0 1) (by simp) with h6575 | h6575
                            · rcases p6546_3 (m.d 0 2) (by simp) with h6576 | h6576
                              · linarith only [h0, h6576, hlam]
                              · rcases p6546_3 (m.d 0 3) (by simp) with h6578 | h6578
                                · linarith only [h1, h6578, hlam]
                                · rcases p6546_3 (m.d 0 4) (by simp) with h6580 | h6580
                                  · linarith only [h2, h6580, hlam]
                                  · rcases p6546_3 (m.d 0 5) (by simp) with h6582 | h6582
                                    · linarith only [h3, h6582, hlam]
                                    · rcases h2bigk with h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c | h6584c
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h4, h6542, h6545, hc12, hc34, hlam, hphi, ht23, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h4, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h3476, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h4023, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h0, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6416, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6418, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6420, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6542, h6545, hc02, hc34, hlam, hphi, ht23, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6542, h6545, hc12, hc34, hlam, hphi, ht23, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6428, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6542, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        rcases p6584_3 (m.d 0 2) (by simp) with h6600 | h6600
                                        · linarith only [h6600, hlam, p6584_0]
                                        · rcases p6584_3 (m.d 1 2) (by simp) with h6602 | h6602
                                          · linarith only [h6418, h6602, hlam]
                                          · rcases p6584_3 (m.d 2 3) (by simp) with h6604 | h6604
                                            · linarith only [h6428, h6604, hlam]
                                            · linarith only [h4, h6604, hlam]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        rcases p6584_3 (m.d 0 2) (by simp) with h6607 | h6607
                                        · linarith only [h3476, h6607, hlam]
                                        · linarith only [h0, h6607, hlam]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h0, h4, h6428, hc12, hc34, hlam, hphi, ht23, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h0, h4023, h6428, hc12, hc34, hlam, hphi, ht23, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        rcases p6584_3 (m.d 0 2) (by simp) with h6613 | h6613
                                        · linarith only [h6613, hlam, p6584_0]
                                        · rcases p6584_3 (m.d 1 2) (by simp) with h6615 | h6615
                                          · linarith only [h6420, h6615, hlam]
                                          · rcases p6584_3 (m.d 2 3) (by simp) with h6617 | h6617
                                            · linarith only [h6542, h6617, hlam]
                                            · linarith only [h4, h6617, hlam]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        rcases p6584_3 (m.d 0 2) (by simp) with h6620 | h6620
                                        · linarith only [h4023, h6620, hlam]
                                        · linarith only [h0, h6620, hlam]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h0, h4, hc12, hc25, hlam, hphi, p6584_1]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [h6544, hlam, p6584_0]
                                      · have p6584_0 := h6584c.1
                                        have p6584_1 := h6584c.2.1
                                        have p6584_2 := h6584c.2.2.1
                                        have p6584_3 := h6584c.2.2.2
                                        linarith only [hlam, p6584_0]
                            · linarith only [h3, h6575, hlam]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h0, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h4, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h3476, hlam, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h4023, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h1, hlam, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h0, h4106, hc12, hc34, hlam, hphi, ht23, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h4106, hlam, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h5969, hlam, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h2, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h0, h6042, hc12, hc45, hlam, hphi, ht23, ht34, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h6042, hc03, hc45, hlam, hphi, ht34, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h6042, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h3, hlam, p6546_0]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h0, h6042, h6428, h6544, hc12, hc34, hlam, hphi, ht23, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h1, h6042, h6416, h6428, h6544, hc12, hc34, hlam, hphi, ht23, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [h2, h6042, h6416, h6422, h6428, h6544, hc12, hc34, hlam, hphi, ht23, p6546_1]
                          · have p6546_0 := h6546c.1
                            have p6546_1 := h6546c.2.1
                            have p6546_2 := h6546c.2.2.1
                            have p6546_3 := h6546c.2.2.2
                            linarith only [hlam, p6546_0]
                        · linarith only [h6428, h6544, h6545, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6648 | h6648
                        · linarith only [h0, h4, h6428, h6544, h6648, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h4, h6428, h6648, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5090000 in
set_option maxHeartbeats 5090000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg4023 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  have h4023 := hg4023
  rcases m.htr 0 3 4 (by decide) (by decide) with h4106 | h4106
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg3476 hg4023 h4106

set_option maxHeartbeats 5256000 in
set_option maxHeartbeats 5256000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s8 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg3476 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h3476 := hg3476
  rcases m.htr 0 2 5 (by decide) (by decide) with h4023 | h4023
  · rcases m.htr 0 3 4 (by decide) (by decide) with h4024 | h4024
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4025 | h4025
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4026 | h4026
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4027 | h4027
          · linarith only [h0, h4, h4027, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4029 | h4029
            · linarith only [h0, h3476, h4029, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4031 | h4031
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4032 | h4032
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4033 | h4033
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4034 | h4034
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4035 | h4035
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h4036 | h4036
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h4037 | h4037
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h4038 | h4038
                            · linarith only [h1, h4032, h4038, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h0bigk with h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h4031, hc01, hlam, hphi, ht0b, ht5b, p4040_1, u5ehi2]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h3476, h4024, h4031, h4037, h4038, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h3476, h4031, h4037, h4038, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                rcases p4040_3 (m.d 0 1) (by simp) with h4045 | h4045
                                · rcases p4040_3 (m.d 0 2) (by simp) with h4046 | h4046
                                  · linarith only [h0, h4046, hlam]
                                  · linarith only [h4023, h4046, hlam]
                                · linarith only [h3, h4045, hlam]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h4, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h3476, hlam, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h3476, h4035, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p4040_1, u5ehi0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h1, hlam, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h4031, h4037, h4038, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h3476, h4, h4031, h4037, h4038, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                rcases p4040_3 (m.d 0 1) (by simp) with h4059 | h4059
                                · rcases p4040_3 (m.d 0 2) (by simp) with h4060 | h4060
                                  · linarith only [h4, h4060, hlam]
                                  · linarith only [h4023, h4060, hlam]
                                · linarith only [h3, h4059, hlam]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h2, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h0, h4031, h4037, h4038, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h4024, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                rcases p4040_3 (m.d 0 1) (by simp) with h4068 | h4068
                                · rcases p4040_3 (m.d 0 2) (by simp) with h4069 | h4069
                                  · linarith only [h3476, h4069, hlam]
                                  · linarith only [h4023, h4069, hlam]
                                · linarith only [h3, h4068, hlam]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h3, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h4023, hlam, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h4025, hlam, p4040_0]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [h4026, hlam, p4040_1]
                              · have p4040_0 := h4040c.1
                                have p4040_1 := h4040c.2.1
                                have p4040_2 := h4040c.2.2.1
                                have p4040_3 := h4040c.2.2.2
                                linarith only [hlam, p4040_0]
                          · linarith only [h0, h3476, h4031, h4037, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                        · linarith only [h0, h3476, h4031, h4035, h4036, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4, h4031, h4035, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4, h4023, h4026, h4029, h4031, h4034, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h4, h4023, h4025, h4027, h4031, h4033, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h4, h4024, h4027, h4031, h4032, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h4, h4023, h4031, hc12, hc23, hlam, hphi]
        · linarith only [h3476, h4023, h4026, hlam]
      · linarith only [h4, h4023, h4025, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h4087 | h4087
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4088 | h4088
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4089 | h4089
          · linarith only [h0, h4, h4089, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h4091 | h4091
            · linarith only [h3476, h4023, h4091, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h4093 | h4093
              · rcases m.htr 1 3 4 (by decide) (by decide) with h4094 | h4094
                · linarith only [h1, h4024, h4094, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h4096 | h4096
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h4097 | h4097
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h4098 | h4098
                      · linarith only [h0, h4, h4024, h4093, h4098, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h4, h4093, h4098, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4, h4023, h4088, h4089, h4093, h4094, h4097, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h4024, h4087, h4089, h4093, h4096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
              · linarith only [h4, h4023, h4024, h4093, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h4, h4023, h4024, h4088, hlam]
      · linarith only [h4, h4023, h4087, hlam]
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s9 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h3476 h4023

end R2N4
