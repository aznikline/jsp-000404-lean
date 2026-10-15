import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3900000 in
set_option maxHeartbeats 3900000 in
theorem r1l7_20_12_14_H_I_L_R_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h658 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h970 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1100 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1223 | h1223
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1224 | h1224
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1225 | h1225
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1226 | h1226
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1227 | h1227
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1228 | h1228
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1229 | h1229
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1230 | h1230
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1231 | h1231
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1232 | h1232
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1233 | h1233
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1234 | h1234
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1235 | h1235
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1236 | h1236
                            · rcases h0bigk with h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h658, hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h970, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1100, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1100, h1226, h1228, hc01, hc12, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1100, h1228, hc01, hc12, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h658, hc01, hc13, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1223, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1223, h1224, h1235, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1237_1, u2ehi4]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1223, h1225, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1237_1, u2ehi4]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1232, h970, hc01, hc13, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1224, hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1226, hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h0, h1223, h1225, h1226, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1237_1, u2ehi4]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1100, h1232, h1233, hc01, hc13, hlam, hphi, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1225, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1227, hlam, p1237_0]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [h1228, hlam, p1237_1]
                              · have p1237_0 := h1237c.1
                                have p1237_1 := h1237c.2.1
                                have p1237_2 := h1237c.2.2.1
                                have p1237_3 := h1237c.2.2.2
                                linarith only [hlam, p1237_0]
                            · rcases h0bigk with h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c | h1263c
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h0, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h658, hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h970, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1100, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h0, h1100, h1228, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1229, h658, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1223, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1224, h1229, h1235, h1236, h658, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1225, h1229, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1263_1, u2ehi4]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1229, h1232, h970, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1224, hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1226, hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1225, h1229, h1232, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1263_1, u2ehi4]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1100, h1229, h1232, h1233, hc01, hc12, hlam, hphi, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1225, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1227, hlam, p1263_0]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [h1228, hlam, p1263_1]
                              · have p1263_0 := h1263c.1
                                have p1263_1 := h1263c.2.1
                                have p1263_2 := h1263c.2.2.1
                                have p1263_3 := h1263c.2.2.2
                                linarith only [hlam, p1263_0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1289 | h1289
                            · linarith only [h1235, h1289, hc34, hlam, hphi, ht23, u2ehi3]
                            · rcases h0bigk with h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c | h1291c
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h0, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h658, hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h970, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1100, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h0, h1228, h1235, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1229, h658, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1223, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1228, h1229, h1235, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi3]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1225, h1229, h1235, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi3]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1229, h1232, h970, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1224, hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1226, hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1225, h1229, h1232, h1235, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1291_1, u2ehi3]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1100, h1229, h1232, h1233, hc01, hc12, hlam, hphi, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1225, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1227, hlam, p1291_0]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [h1228, hlam, p1291_1]
                              · have p1291_0 := h1291c.1
                                have p1291_1 := h1291c.2.1
                                have p1291_2 := h1291c.2.2.1
                                have p1291_3 := h1291c.2.2.2
                                linarith only [hlam, p1291_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1317 | h1317
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1318 | h1318
                            · rcases h0bigk with h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c | h1319c
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h658, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h970, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1100, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h970, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1229, h658, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1223, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1224, h1229, h1234, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1319_1, u2ehi2]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1225, h1229, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1319_1, u2ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1229, h1232, h970, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1224, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1226, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1225, h1229, h1232, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1319_1, u2ehi4]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1100, h1229, h1232, h1233, hc01, hc12, hlam, hphi, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1225, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1227, hlam, p1319_0]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [h1228, hlam, p1319_1]
                              · have p1319_0 := h1319c.1
                                have p1319_1 := h1319c.2.1
                                have p1319_2 := h1319c.2.2.1
                                have p1319_3 := h1319c.2.2.2
                                linarith only [hlam, p1319_0]
                            · linarith only [h1234, h1317, h1318, hc24, hlam, hphi, u2ehi2]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1346 | h1346
                            · linarith only [h1226, h1229, h1317, h1346, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h1228, h1229, h1232, h1234, h1346, h970, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1228, h1233, h970, hlam]
                    · linarith only [h1226, h1232, h658, hlam]
                  · linarith only [h0, h1223, h1231, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1225, h1230, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1225, h1229, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1354 | h1354
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1355 | h1355
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1356 | h1356
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1357 | h1357
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1358 | h1358
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1359 | h1359
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1360 | h1360
                          · linarith only [h0, h1223, h1228, h1359, h1360, h970, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1362 | h1362
                            · linarith only [h1224, h1228, h1359, h1362, hlam]
                            · rcases h0bigk with h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c | h1364c
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, hlam, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h658, hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h970, hlam, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1100, hlam, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, h1224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1364_1, u2ehi3]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, h1224, h1228, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1364_1, u2ehi3]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h658, hc01, hc13, hlam, hphi, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1223, hlam, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, h1223, h1224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1364_1, u2ehi3]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h0, h1223, h1224, h1228, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1364_1, u2ehi3]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1228, h1358, hc01, hc14, hlam, hphi, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1224, hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1226, hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1228, hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1100, h1358, hc01, hc14, hlam, hphi, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1225, hlam, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1227, hlam, p1364_0]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [h1228, h1358, hc04, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1364_1]
                              · have p1364_0 := h1364c.1
                                have p1364_1 := h1364c.2.1
                                have p1364_2 := h1364c.2.2.1
                                have p1364_3 := h1364c.2.2.2
                                linarith only [hlam, p1364_0]
                        · linarith only [h1226, h1228, h1354, h1357, h1358, h1359, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1391 | h1391
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1392 | h1392
                          · linarith only [h1358, h1391, h1392, h970, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1394 | h1394
                            · linarith only [h1224, h1358, h1391, h1394, h970, hlam]
                            · rcases h0bigk with h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c | h1396c
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h0, hlam, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h658, hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h970, hlam, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1100, hlam, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h0, h658, hc01, hc12, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h0, h1224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1396_1, u2ehi3]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1354, h658, hc01, hc12, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1223, hlam, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1224, h1354, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1396_1, u2ehi3]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1225, h1354, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1396_1, u2ehi4]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1224, hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1226, hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1228, hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1100, hc01, hc15, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1225, hlam, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1227, hlam, p1396_0]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [h1228, hc04, hc45, hlam, hphi, p1396_1]
                              · have p1396_0 := h1396c.1
                                have p1396_1 := h1396c.2.1
                                have p1396_2 := h1396c.2.2.1
                                have p1396_3 := h1396c.2.2.2
                                linarith only [hlam, p1396_0]
                        · linarith only [h1226, h1358, h1391, h970, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1226, h1228, h1357, h658, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h1223, h1356, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1223, h1355, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1223, h1354, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1427 | h1427
            · linarith only [h1226, h1227, h1427, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1434 | h1434
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1435 | h1435
                          · linarith only [h0, h1223, h1427, h1434, h1435, h970, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1437 | h1437
                            · linarith only [h1223, h1224, h1227, h1427, h1434, h1437, hc35, hlam, hphi, ht23, u2ehi3]
                            · rcases h0bigk with h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c | h1439c
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h0, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h658, hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h970, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1100, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h0, h1224, h1226, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h0, h1224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h0, h1224, h1226, h1227, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1227, h1432, h1433, h1437, hc01, hc13, hlam, hphi, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1223, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1227, h1432, h1433, h1437, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1227, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1432, h970, hc01, hc13, hlam, hphi, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1224, hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1226, hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1427, hlam, p1439_0]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1100, h1432, h1433, hc01, hc13, hlam, hphi, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1225, hlam, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1227, h1432, h1433, h1437, hc03, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1439_1]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [h1224, h1227, h1432, h1433, h1437, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1439_1, u2ehi3]
                              · have p1439_0 := h1439c.1
                                have p1439_1 := h1439c.2.1
                                have p1439_2 := h1439c.2.2.1
                                have p1439_3 := h1439c.2.2.2
                                linarith only [hlam, p1439_0]
                        · linarith only [h1226, h1227, h1434, hc35, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1466 | h1466
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1467 | h1467
                          · linarith only [h1433, h1466, h1467, h970, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1469 | h1469
                            · linarith only [h1224, h1433, h1466, h1469, h970, hc23, hlam, hphi, u2ehi3]
                            · rcases h0bigk with h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c | h1471c
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h0, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h658, hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h970, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1100, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h0, h1223, h1466, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h0, h1224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1471_1, u2ehi3]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1429, h658, hc01, hc12, hlam, hphi, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1223, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1224, h1429, h658, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1471_1, u2ehi3]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1227, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1224, hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1226, hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1427, hlam, p1471_0]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1100, h1433, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1225, hlam, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1100, h1433, hc03, hc45, hlam, hphi, ht34, p1471_1]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [h1100, h1224, h1433, hc45, hlam, hphi, ht23, ht34, p1471_1, u2ehi3]
                              · have p1471_0 := h1471c.1
                                have p1471_1 := h1471c.2.1
                                have p1471_2 := h1471c.2.2.1
                                have p1471_3 := h1471c.2.2.2
                                linarith only [hlam, p1471_0]
                        · linarith only [h1226, h1433, h1466, h970, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1226, h1432, h658, hlam]
                  · linarith only [h0, h1223, h1431, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1223, h1430, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1225, h1429, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1502 | h1502
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1503 | h1503
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1504 | h1504
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1505 | h1505
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1506 | h1506
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1507 | h1507
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1508 | h1508
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1509 | h1509
                        · linarith only [h1225, h1226, h1502, h1509, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1511 | h1511
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1512 | h1512
                            · rcases h0bigk with h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c | h1513c
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h0, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h658, hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h970, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1100, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h0, h1502, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h0, h1225, h1226, h1502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1513_1, u2ehi4]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h0, h1225, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1513_1, u2ehi4]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1504, h658, hc01, hc12, hlam, hphi, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1223, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1226, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1225, h1226, h1504, h1507, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1513_1, u2ehi4]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1226, h1504, h1507, hc01, hc12, hlam, hphi, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1224, hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1226, h1504, h1507, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1225, h1226, h1504, h1507, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1513_1, u2ehi4]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1502, h1504, h658, hc01, hc12, hlam, hphi, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1225, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1502, hlam, p1513_0]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [h1503, hlam, p1513_1]
                              · have p1513_0 := h1513c.1
                                have p1513_1 := h1513c.2.1
                                have p1513_2 := h1513c.2.2.1
                                have p1513_3 := h1513c.2.2.2
                                linarith only [hlam, p1513_0]
                            · linarith only [h1226, h1511, h1512, h658, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h1226, h1502, h1503, h1504, h1507, h1511, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1226, h1502, h1503, h1507, h1508, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1542 | h1542
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1543 | h1543
                        · linarith only [h1507, h1543, h658, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1545 | h1545
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1546 | h1546
                            · rcases h0bigk with h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c | h1547c
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h0, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h658, hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h970, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1100, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h0, h1225, h1502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi4]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h0, h970, hc01, hc12, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h0, h1225, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1547_1, u2ehi4]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h658, hc01, hc13, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1223, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1226, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1507, h658, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1224, hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1226, hc03, hc34, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1225, h1226, hc34, hlam, hphi, ht23, p1547_1, u2ehi4]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1100, hc01, hc15, hlam, hphi, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1225, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1502, hlam, p1547_0]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [h1503, hlam, p1547_1]
                              · have p1547_0 := h1547c.1
                                have p1547_1 := h1547c.2.1
                                have p1547_2 := h1547c.2.2.1
                                have p1547_3 := h1547c.2.2.2
                                linarith only [hlam, p1547_0]
                            · linarith only [h1507, h1546, h658, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h1226, h1503, h1545, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h1226, h1502, h1503, h1542, h970, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h1223, h1506, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1223, h1505, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1223, h1504, hlam]
            · linarith only [h1226, h1502, h1503, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1580 | h1580
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1581 | h1581
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1582 | h1582
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1583 | h1583
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1585 | h1585
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1586 | h1586
                        · linarith only [h0, h1223, h1226, h1586, h658, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1588 | h1588
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1589 | h1589
                            · rcases h0bigk with h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c | h1590c
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h0, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h658, hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h970, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1100, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h0, h1223, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h0, h1223, h1502, h1580, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h0, h1223, h1502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1502, h1584, h1589, hc01, hc13, hlam, hphi, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1223, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1226, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1502, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1224, hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1223, h1226, h1584, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [hlam, p1590_0]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1223, h1226, h1502, h1584, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1100, hc01, hc15, hlam, hphi, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1225, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1223, h1502, hc35, hlam, hphi, ht23, p1590_1, u2ehi2]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [h1580, hlam, p1590_1]
                              · have p1590_0 := h1590c.1
                                have p1590_1 := h1590c.2.1
                                have p1590_2 := h1590c.2.2.1
                                have p1590_3 := h1590c.2.2.2
                                linarith only [hlam, p1590_0]
                            · linarith only [h1223, h1226, h1589, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h1226, h1580, h1586, h1588, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h1226, h1580, h1581, h1584, h1585, h970, hc01, hc12, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1619 | h1619
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1620 | h1620
                        · linarith only [h1584, h1620, h658, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1622 | h1622
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1623 | h1623
                            · rcases h0bigk with h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c | h1624c
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h0, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h658, hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h970, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1100, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h0, h1223, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1624_1, u2ehi2]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h0, h970, hc01, hc12, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h0, h1100, hc01, hc12, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h658, hc01, hc13, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1223, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1226, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1502, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1224, hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1226, hc03, hc34, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [hlam, p1624_0]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1223, h1226, h1502, hc34, hlam, hphi, ht23, p1624_1, u2ehi2]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1100, h1619, hc01, hc14, hlam, hphi, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1225, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1223, h1502, h1623, hc34, hlam, hphi, ht23, p1624_1, u2ehi2]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [h1580, hlam, p1624_1]
                              · have p1624_0 := h1624c.1
                                have p1624_1 := h1624c.2.1
                                have p1624_2 := h1624c.2.2.1
                                have p1624_3 := h1624c.2.2.2
                                linarith only [hlam, p1624_0]
                            · linarith only [h1584, h1622, h1623, h658, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h1226, h1580, h1622, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h1580, h1619, h970, hlam]
                  · linarith only [h0, h1223, h1583, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1223, h1582, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h1223, h1581, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1657 | h1657
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1658 | h1658
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1659 | h1659
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1660 | h1660
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1661 | h1661
                        · linarith only [h1223, h1226, h1661, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1663 | h1663
                          · linarith only [h0, h1224, h1580, h1663, h970, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1665 | h1665
                            · linarith only [h1223, h1226, h1580, h1665, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1223, h1226, h1660, h1665, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1223, h1226, h1659, h1660, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1669 | h1669
                      · linarith only [h1223, h1226, h1580, h1659, h1669, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1671 | h1671
                        · linarith only [h1223, h1226, h1671, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1673 | h1673
                          · linarith only [h1669, h1673, h970, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1675 | h1675
                            · linarith only [h1223, h1226, h1669, h1675, h970, hc34, hlam, hphi, ht23, u2ehi2]
                            · linarith only [h1223, h1226, h1675, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h1223, h1658, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h1224, h1657, hlam]
              · linarith only [h0, h1223, h1656, hlam]
      · linarith only [h1223, h1225, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1223, h1224, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1683 | h1683
    · linarith only [h1223, h1683, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1685 | h1685
      · linarith only [h1223, h1685, hc23, hlam, hphi, u2ehi4]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1687 | h1687
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1688 | h1688
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1689 | h1689
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1690 | h1690
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1691 | h1691
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1692 | h1692
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1693 | h1693
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1694 | h1694
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1695 | h1695
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1696 | h1696
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1697 | h1697
                            · rcases h0bigk with h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c | h1698c
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h0, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h658, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h970, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1100, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1685, h1690, h1695, h1696, hc01, hc12, hlam, hphi, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1223, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1683, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1685, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h658, hc01, hc13, hlam, hphi, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1223, h1690, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1223, h1685, h1689, h1690, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1223, h1685, h1690, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1683, h1690, h1695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1687, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1683, h1685, h1690, h1695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1100, hc01, hc15, hlam, hphi, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1685, h1690, h1695, h1696, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1698_1, u2ehi0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1688, hlam, p1698_0]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [h1689, hlam, p1698_1]
                              · have p1698_0 := h1698c.1
                                have p1698_1 := h1698c.2.1
                                have p1698_2 := h1698c.2.2.1
                                have p1698_3 := h1698c.2.2.2
                                linarith only [hlam, p1698_0]
                            · rcases h0bigk with h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h0, hlam, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h658, hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h970, hlam, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1100, hlam, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1223, hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1683, hlam, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1685, hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1223, h1690, hc01, hc12, hlam, hphi, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1223, h1690, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1724_1, u2ehi0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1223, h1690, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1223, h1690, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1690, h1693, h970, hc01, hc12, hlam, hphi, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1683, h1690, h1695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1724_1, u2ehi0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1687, hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1683, h1685, h1690, h1695, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1724_1, u2ehi0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1100, h1690, h1693, h1694, hc01, hc12, hlam, hphi, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1685, h1690, h1695, h1696, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1724_1, u2ehi0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1688, hlam, p1724_0]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [h1689, hlam, p1724_1]
                              · have p1724_0 := h1724c.1
                                have p1724_1 := h1724c.2.1
                                have p1724_2 := h1724c.2.2.1
                                have p1724_3 := h1724c.2.2.2
                                linarith only [hlam, p1724_0]
                          · linarith only [h1683, h1696, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1223, h1695, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1689, h1694, h970, hlam]
                    · linarith only [h1223, h1687, h1690, h1693, h658, hc01, hc12, hlam, hphi]
                  · linarith only [h1690, h1692, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1223, h1690, h1691, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1756 | h1756
                · linarith only [h1690, h1756, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1758 | h1758
                  · linarith only [h1690, h1758, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1760 | h1760
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1761 | h1761
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1762 | h1762
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1763 | h1763
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1764 | h1764
                            · rcases h0bigk with h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c | h1765c
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h0, hlam, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h658, hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h970, hlam, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1100, hlam, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h0, h1758, h1762, h1763, hc01, hc23, hlam, hphi, ht12, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1223, hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1683, hlam, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1685, hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1690, h658, hc01, hc23, hlam, hphi, ht12, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1690, h658, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1685, h1689, h1690, h658, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1685, h1690, h658, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h970, hc01, hc14, hlam, hphi, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1683, h1762, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1687, hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1685, h1687, h1690, h658, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1100, hc01, hc15, hlam, hphi, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1685, h1762, h1763, hc23, hlam, hphi, p1765_1, u2ehi0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1688, hlam, p1765_0]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [h1689, hlam, p1765_1]
                              · have p1765_0 := h1765c.1
                                have p1765_1 := h1765c.2.1
                                have p1765_2 := h1765c.2.2.1
                                have p1765_3 := h1765c.2.2.2
                                linarith only [hlam, p1765_0]
                            · rcases h0bigk with h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h0, hlam, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h658, hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h970, hlam, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1100, hlam, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h0, h1758, h1762, h1763, hc01, hc23, hlam, hphi, ht12, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1223, hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1683, hlam, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1685, hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1690, h658, hc01, hc23, hlam, hphi, ht12, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1690, h658, hc23, hlam, hphi, p1791_1, u2ehi0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1689, h1690, h1764, h658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1100, h1690, h658, hc01, hc23, hlam, hphi, ht12, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1756, h1762, h970, hc01, hc23, hlam, hphi, ht12, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1756, h1762, h970, hc23, hlam, hphi, p1791_1, u2ehi0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1687, hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1685, h1756, h1762, h970, hc23, hlam, hphi, p1791_1, u2ehi0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1100, h1758, h1762, h1763, hc01, hc23, hlam, hphi, ht12, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1100, h1758, h1762, h1763, hc23, hlam, hphi, p1791_1, u2ehi0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1688, hlam, p1791_0]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [h1689, hlam, p1791_1]
                              · have p1791_0 := h1791c.1
                                have p1791_1 := h1791c.2.1
                                have p1791_2 := h1791c.2.2.1
                                have p1791_3 := h1791c.2.2.2
                                linarith only [hlam, p1791_0]
                          · linarith only [h1683, h1763, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h0, h1690, h1762, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1687, h1689, h1761, h658, h970, hc01, hc13, hlam, hphi]
                    · linarith only [h1687, h1760, h658, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1821 | h1821
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1822 | h1822
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1823 | h1823
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1824 | h1824
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1825 | h1825
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1826 | h1826
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1827 | h1827
                          · linarith only [h1683, h1689, h1821, h1826, h1827, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1683, h1827, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1223, h1687, h1826, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h1683, h1822, h1825, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1685, h1687, h1689, h1823, h1824, h658, hc01, hc12, hlam, hphi]
                  · linarith only [h1821, h1823, hc25, hlam, hphi, u2ehi2]
                · linarith only [h1223, h1821, h1822, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1835 | h1835
                · linarith only [h1821, h1835, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1837 | h1837
                  · linarith only [h1821, h1837, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1840 | h1840
                      · linarith only [h1683, h1689, h1835, h1840, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1842 | h1842
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1843 | h1843
                          · linarith only [h1683, h1840, h1842, h1843, h970, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1683, h1843, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1223, h1687, h1842, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1687, h1839, h658, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1848 | h1848
            · linarith only [h1687, h1688, h1848, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1850 | h1850
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1851 | h1851
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1852 | h1852
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1853 | h1853
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1854 | h1854
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1855 | h1855
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1856 | h1856
                          · linarith only [h1683, h1848, h1855, h1856, hc23, hlam, hphi, u2ehi0]
                          · linarith only [h1683, h1853, h1854, h1856, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1687, h1688, h1855, hc23, hc35, hlam, hphi]
                      · linarith only [h1683, h1851, h1854, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1687, h1688, h1853, hc13, hc35, hlam, hphi]
                  · linarith only [h1223, h1850, h1852, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1223, h1850, h1851, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1864 | h1864
                · linarith only [h1850, h1864, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1866 | h1866
                  · linarith only [h1850, h1866, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1868 | h1868
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1869 | h1869
                      · linarith only [h1683, h1848, h1850, h1868, h1869, hc23, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1871 | h1871
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1872 | h1872
                          · linarith only [h0, h1864, h1869, h1872, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h1683, h1872, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                        · linarith only [h1687, h1688, h1850, h1871, hc13, hc35, hlam, hphi]
                    · linarith only [h1687, h1868, h658, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1877 | h1877
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1878 | h1878
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1879 | h1879
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1880 | h1880
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1881 | h1881
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1882 | h1882
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1883 | h1883
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1884 | h1884
                        · linarith only [h1687, h1877, h1879, h1884, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1223, h1884, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1878, h1883, h970, hlam]
                    · linarith only [h1223, h1879, h1882, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1880, h1881, hc25, hlam, hphi, u2ehi3]
                · linarith only [h1223, h1879, h1880, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1891 | h1891
                · linarith only [h1879, h1891, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1893 | h1893
                  · linarith only [h1879, h1893, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1895 | h1895
                    · linarith only [h1685, h1687, h1877, h1879, h1895, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1897 | h1897
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1898 | h1898
                        · linarith only [h1879, h1895, h1898, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1223, h1898, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1878, h1897, h970, hlam]
            · linarith only [h1687, h1877, h1878, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1903 | h1903
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1904 | h1904
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1905 | h1905
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1906 | h1906
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1907 | h1907
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1908 | h1908
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1909 | h1909
                        · linarith only [h1223, h1687, h1904, h1909, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1223, h1909, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1903, h1908, h970, hlam]
                    · linarith only [h1223, h1904, h1907, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1223, h1904, h1906, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1223, h1904, h1905, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1916 | h1916
                · linarith only [h1904, h1916, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1918 | h1918
                  · linarith only [h1904, h1918, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1920 | h1920
                    · linarith only [h1223, h1687, h1904, h1920, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1922 | h1922
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1923 | h1923
                        · linarith only [h1223, h1920, h1923, h658, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1223, h1923, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1903, h1922, h970, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1927 | h1927
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1928 | h1928
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1929 | h1929
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1930 | h1930
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1931 | h1931
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1932 | h1932
                        · linarith only [h1223, h1687, h1927, h1932, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1223, h1932, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h1683, h1928, h1931, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1223, h1927, h1930, hc34, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1223, h1927, h1929, hc25, hlam, hphi, u2ehi0]
                · linarith only [h1223, h1927, h1928, hc24, hlam, hphi, u2ehi0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                · linarith only [h1927, h1939, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1941 | h1941
                  · linarith only [h1927, h1941, hc23, hlam, hphi, u2ehi4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
                    · linarith only [h1223, h1687, h1927, h1943, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1945 | h1945
                      · linarith only [h1223, h1687, h1903, h1939, h1945, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1947 | h1947
                        · linarith only [h1223, h1687, h1947, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1223, h1947, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
