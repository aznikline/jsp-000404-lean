import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 1 2 3 (by decide) (by decide) with h1224 | h1224
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1225 | h1225
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1226 | h1226
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1227 | h1227
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1228 | h1228
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1229 | h1229
            · linarith only [h1229, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1231 | h1231
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1232 | h1232
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1233 | h1233
                  · linarith only [h1224, h1231, h1233, h2, h9, hc12, hlam, hphi, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1235 | h1235
                    · linarith only [h0, h1224, h1231, h1235, h2, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                    · rcases h2bigk with h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1224, h1232, h1235, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        rcases p1237_3 (m.d 0 2) (by simp) with h1240 | h1240
                        · rcases p1237_3 (m.d 1 2) (by simp) with h1241 | h1241
                          · linarith only [h0, h1241, hlam]
                          · linarith only [h1224, h1241, hlam]
                        · linarith only [h1240, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        rcases p1237_3 (m.d 0 2) (by simp) with h1245 | h1245
                        · rcases p1237_3 (m.d 1 2) (by simp) with h1246 | h1246
                          · linarith only [h0, h1246, hlam]
                          · linarith only [h1225, h1246, hlam]
                        · linarith only [h1245, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        rcases p1237_3 (m.d 0 2) (by simp) with h1250 | h1250
                        · rcases p1237_3 (m.d 1 2) (by simp) with h1251 | h1251
                          · linarith only [h0, h1251, hlam]
                          · linarith only [h1226, h1251, hlam]
                        · linarith only [h1250, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h0, hlam, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h0, h1232, h1235, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        rcases p1237_3 (m.d 0 2) (by simp) with h1258 | h1258
                        · rcases p1237_3 (m.d 1 2) (by simp) with h1259 | h1259
                          · rcases p1237_3 (m.d 2 3) (by simp) with h1260 | h1260
                            · linarith only [h1224, h1260, hlam]
                            · linarith only [h1231, h1260, hlam]
                          · linarith only [h1259, hlam, p1237_0]
                        · linarith only [h1258, h5, hlam]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        rcases p1237_3 (m.d 0 2) (by simp) with h1265 | h1265
                        · rcases p1237_3 (m.d 1 2) (by simp) with h1266 | h1266
                          · rcases p1237_3 (m.d 2 3) (by simp) with h1267 | h1267
                            · linarith only [h1224, h1267, hlam]
                            · linarith only [h1232, h1267, hlam]
                          · linarith only [h1266, hlam, p1237_0]
                        · linarith only [h1265, h6, hlam]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h4, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1224, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h0, h1224, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h0, h1224, hc01, hc25, hlam, hphi, ht0b, ht5b, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h5, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1225, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1231, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1233, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h6, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1226, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h1232, hlam, p1237_0]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [h0, h1226, h1231, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                      · have p1237_0 := h1237c.1
                        have p1237_1 := h1237c.2.1
                        have p1237_2 := h1237c.2.2.1
                        have p1237_3 := h1237c.2.2.2
                        linarith only [hlam, p1237_0]
                · linarith only [h0, h1224, h1228, h1231, h1232, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1288 | h1288
                · linarith only [h0, h1224, h1227, h1231, h1288, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1290 | h1290
                  · linarith only [h1290, h2, h9, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1292 | h1292
                    · linarith only [h1227, h1292, h2, h9, hlam]
                    · rcases h2bigk with h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c | h1294c
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h0, h1224, h1227, h1231, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1297 | h1297
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1298 | h1298
                          · linarith only [h0, h1298, hlam]
                          · linarith only [h1224, h1298, hlam]
                        · linarith only [h1297, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1302 | h1302
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1303 | h1303
                          · linarith only [h0, h1303, hlam]
                          · linarith only [h1225, h1303, hlam]
                        · linarith only [h1302, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1307 | h1307
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1308 | h1308
                          · linarith only [h0, h1308, hlam]
                          · linarith only [h1226, h1308, hlam]
                        · linarith only [h1307, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h0, hlam, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1314 | h1314
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1315 | h1315
                          · rcases p1294_3 (m.d 2 3) (by simp) with h1316 | h1316
                            · linarith only [h1316, hlam, p1294_0]
                            · rcases p1294_3 (m.d 2 4) (by simp) with h1318 | h1318
                              · linarith only [h1225, h1318, hlam]
                              · linarith only [h1231, h1318, hlam]
                          · linarith only [h1315, hlam, p1294_0]
                        · linarith only [h1314, h4, hlam]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1323 | h1323
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1324 | h1324
                          · rcases p1294_3 (m.d 2 3) (by simp) with h1325 | h1325
                            · linarith only [h1224, h1325, hlam]
                            · rcases p1294_3 (m.d 2 4) (by simp) with h1327 | h1327
                              · linarith only [h1327, hlam, p1294_0]
                              · rcases p1294_3 (m.d 2 5) (by simp) with h1329 | h1329
                                · linarith only [h1226, h1329, hlam]
                                · linarith only [h1290, h1329, hlam]
                          · linarith only [h1324, hlam, p1294_0]
                        · linarith only [h1323, h5, hlam]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        rcases p1294_3 (m.d 0 2) (by simp) with h1334 | h1334
                        · rcases p1294_3 (m.d 1 2) (by simp) with h1335 | h1335
                          · rcases p1294_3 (m.d 2 3) (by simp) with h1336 | h1336
                            · linarith only [h1224, h1336, hlam]
                            · rcases p1294_3 (m.d 2 4) (by simp) with h1338 | h1338
                              · linarith only [h1225, h1338, hlam]
                              · rcases p1294_3 (m.d 2 5) (by simp) with h1340 | h1340
                                · linarith only [h1340, hlam, p1294_0]
                                · rcases h2emax with h1342 | h1342 | h1342 | h1342 | h1342
                                  · linarith only [h0, h1224, h1228, h1231, h1292, h1342, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                  · linarith only [h1224, h1228, h1231, h1292, h1342, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                  · rcases h4bigk with h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c | h1345c
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, p1345_1, u1ehi3]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h9, hc24, hc45, hlam, hphi, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1231, h9, hc23, hc45, hlam, hphi, ht34, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h9, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h2, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h2, h9, hc24, hc45, hlam, hphi, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1231, h2, h9, hc23, hc45, hlam, hphi, ht34, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1229, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h5, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1225, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1231, hlam, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1290, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h7, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1227, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h0, h1224, h1228, h1292, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1292, hlam, p1345_0]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p1345_1, u1ehi3]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1227, h1231, hc23, hc45, hlam, hphi, ht34, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      rcases p1345_3 (m.d 0 4) (by simp) with h1368 | h1368
                                      · linarith only [h1368, h9, hlam]
                                      · linarith only [h1368, h5, hlam]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [h1231, hc23, hc45, hlam, hphi, ht34, p1345_1]
                                    · have p1345_0 := h1345c.1
                                      have p1345_1 := h1345c.2.1
                                      have p1345_2 := h1345c.2.2.1
                                      have p1345_3 := h1345c.2.2.2
                                      linarith only [hlam, p1345_0]
                                  · rcases h4bigk with h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c | h1373c
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, p1373_1, u1ehi3]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h9, hc24, hc45, hlam, hphi, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1231, h9, hc23, hc45, hlam, hphi, ht34, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h9, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h2, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h2, h9, hc24, hc45, hlam, hphi, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1231, h2, h9, hc23, hc45, hlam, hphi, ht34, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1229, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h5, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1225, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1231, hlam, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1290, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h7, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1227, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h0, h1224, h1228, h1292, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1292, hlam, p1373_0]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p1373_1, u1ehi3]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1227, h1231, hc23, hc45, hlam, hphi, ht34, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      rcases p1373_3 (m.d 0 4) (by simp) with h1396 | h1396
                                      · linarith only [h1396, h9, hlam]
                                      · linarith only [h1396, h5, hlam]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [h1231, hc23, hc45, hlam, hphi, ht34, p1373_1]
                                    · have p1373_0 := h1373c.1
                                      have p1373_1 := h1373c.2.1
                                      have p1373_2 := h1373c.2.2.1
                                      have p1373_3 := h1373c.2.2.2
                                      linarith only [hlam, p1373_0]
                                  · rcases h4bigk with h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c | h1401c
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h9, hc45, hlam, hphi, ht12, ht23, ht34, p1401_1, u1ehi3]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h9, hc24, hc45, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1231, h9, hc23, hc45, hlam, hphi, ht34, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h9, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h2, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h2, h9, hc24, hc45, hlam, hphi, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1231, h2, h9, hc23, hc45, hlam, hphi, ht34, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1229, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h5, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1225, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1231, hlam, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1290, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h7, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1227, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h0, h1224, h1228, h1292, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1292, hlam, p1401_0]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h2, hc45, hlam, hphi, ht12, ht23, ht34, p1401_1, u1ehi3]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1227, h1231, hc23, hc45, hlam, hphi, ht34, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      rcases p1401_3 (m.d 0 4) (by simp) with h1424 | h1424
                                      · linarith only [h1424, h9, hlam]
                                      · linarith only [h1424, h5, hlam]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [h1231, hc23, hc45, hlam, hphi, ht34, p1401_1]
                                    · have p1401_0 := h1401c.1
                                      have p1401_1 := h1401c.2.1
                                      have p1401_2 := h1401c.2.2.1
                                      have p1401_3 := h1401c.2.2.2
                                      linarith only [hlam, p1401_0]
                          · linarith only [h1335, hlam, p1294_0]
                        · linarith only [h1334, h6, hlam]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h4, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1224, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1231, hlam, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1288, hlam, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h5, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1225, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h5, h9, hc23, hc45, hlam, hphi, ht34, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1290, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h6, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1226, hlam, p1294_0]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h0, h1226, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [h1, h1228, h1288, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1294_1]
                      · have p1294_0 := h1294c.1
                        have p1294_1 := h1294c.2.1
                        have p1294_2 := h1294c.2.2.1
                        have p1294_3 := h1294c.2.2.2
                        linarith only [hlam, p1294_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1446 | h1446
            · linarith only [h0, h1227, h1228, h1446, h4, h8, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1448 | h1448
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1449 | h1449
                · linarith only [h1227, h1228, h1449, hc23, hlam, hphi, ht12, u1ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1451 | h1451
                  · linarith only [h1227, h1228, h1451, h8, h9, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1453 | h1453
                    · linarith only [h1453, h2, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h2bigk with h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1224, h1448, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        rcases p1455_3 (m.d 0 2) (by simp) with h1458 | h1458
                        · rcases p1455_3 (m.d 1 2) (by simp) with h1459 | h1459
                          · linarith only [h0, h1459, hlam]
                          · linarith only [h1224, h1459, hlam]
                        · linarith only [h1458, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        rcases p1455_3 (m.d 0 2) (by simp) with h1463 | h1463
                        · rcases p1455_3 (m.d 1 2) (by simp) with h1464 | h1464
                          · linarith only [h0, h1464, hlam]
                          · linarith only [h1225, h1464, hlam]
                        · linarith only [h1463, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        rcases p1455_3 (m.d 0 2) (by simp) with h1468 | h1468
                        · rcases p1455_3 (m.d 1 2) (by simp) with h1469 | h1469
                          · linarith only [h0, h1469, hlam]
                          · linarith only [h1226, h1469, hlam]
                        · linarith only [h1468, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, hlam, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1448, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        rcases p1455_3 (m.d 0 2) (by simp) with h1476 | h1476
                        · rcases p1455_3 (m.d 1 2) (by simp) with h1477 | h1477
                          · rcases p1455_3 (m.d 2 3) (by simp) with h1478 | h1478
                            · linarith only [h1224, h1478, hlam]
                            · linarith only [h1448, h1478, hlam]
                          · linarith only [h1477, hlam, p1455_0]
                        · linarith only [h1476, h5, hlam]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1448, h1449, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h4, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1224, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1224, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1449, hlam, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h5, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1225, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1448, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1451, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h6, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h1226, hlam, p1455_0]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1226, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [h0, h1226, h1448, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1455_1]
                      · have p1455_0 := h1455c.1
                        have p1455_1 := h1455c.2.1
                        have p1455_2 := h1455c.2.2.1
                        have p1455_3 := h1455c.2.2.2
                        linarith only [hlam, p1455_0]
              · linarith only [h0, h1227, h1228, h1448, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1227, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1501 | h1501
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1502 | h1502
          · linarith only [h1224, h1226, h1502, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
            · linarith only [h1504, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
              · linarith only [h0, h1224, h1226, h1506, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1501, h1502, h1506, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · linarith only [h1501, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
    · linarith only [h1225, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1511 | h1511
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1512 | h1512
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1513 | h1513
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1514 | h1514
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1515 | h1515
            · linarith only [h1515, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1517 | h1517
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1518 | h1518
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1519 | h1519
                  · linarith only [h1519, h2, h9, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1521 | h1521
                    · linarith only [h1521, h2, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · rcases h2bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        rcases p1523_3 (m.d 0 2) (by simp) with h1525 | h1525
                        · rcases p1523_3 (m.d 1 2) (by simp) with h1526 | h1526
                          · linarith only [h0, h1526, hlam]
                          · rcases p1523_3 (m.d 2 3) (by simp) with h1528 | h1528
                            · linarith only [h1528, h4, hlam]
                            · linarith only [h1224, h1528, hlam]
                        · linarith only [h0, h1525, hlam]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h0, h1224, h1512, h1515, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1523_1, u1ehi3]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1224, h1512, h1519, h4, hlam, p1523_2]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1224, h1512, h4, hlam, p1523_2]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h0, hlam, p1523_1]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1224, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1224, h4, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1523_1]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1224, h4, hc02, hc25, hlam, hphi, ht0b, ht5b, p1523_1]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h4, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h4, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1523_1, u1ehi1]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        rcases p1523_3 (m.d 0 2) (by simp) with h1543 | h1543
                        · rcases p1523_3 (m.d 1 2) (by simp) with h1544 | h1544
                          · linarith only [h1224, h1544, hlam]
                          · linarith only [h1511, h1544, hlam]
                        · linarith only [h1543, h5, hlam]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        rcases p1523_3 (m.d 0 2) (by simp) with h1548 | h1548
                        · rcases p1523_3 (m.d 1 2) (by simp) with h1549 | h1549
                          · linarith only [h1224, h1549, hlam]
                          · linarith only [h1512, h1549, hlam]
                        · linarith only [h1548, h6, hlam]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h5, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1511, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1517, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1519, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h6, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1512, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h1518, hlam, p1523_0]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [h0, h1512, h1517, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1523_1]
                      · have p1523_0 := h1523c.1
                        have p1523_1 := h1523c.2.1
                        have p1523_2 := h1523c.2.2.1
                        have p1523_3 := h1523c.2.2.2
                        linarith only [hlam, p1523_0]
                · linarith only [h1224, h1518, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · linarith only [h1224, h1512, h1515, h1517, hc34, hlam, hphi, ht12, ht23, u1ehi3]
          · linarith only [h1224, h1512, h1514, hlam]
        · linarith only [h1224, h1513, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1568 | h1568
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
            · linarith only [h1569, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1571 | h1571
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1572 | h1572
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1573 | h1573
                  · linarith only [h0, h1511, h1512, h1572, h1573, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1575 | h1575
                    · linarith only [h1511, h1512, h1571, h1575, h6, h9, hlam]
                    · rcases h2bigk with h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        rcases p1577_3 (m.d 0 2) (by simp) with h1579 | h1579
                        · rcases p1577_3 (m.d 1 2) (by simp) with h1580 | h1580
                          · linarith only [h0, h1580, hlam]
                          · rcases p1577_3 (m.d 2 3) (by simp) with h1582 | h1582
                            · linarith only [h1582, h4, hlam]
                            · linarith only [h1224, h1582, hlam]
                        · linarith only [h0, h1579, hlam]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h0, h1511, h1512, h1572, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1577_1, u1ehi3]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1511, h1512, h1572, h4, hlam, p1577_2]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1511, h1512, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1577_1, u1ehi3]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h0, hlam, p1577_1]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1224, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1512, h1571, h6, h9, hc34, hc45, hlam, hphi, p1577_1]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1512, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h4, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h0, h1511, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1577_1, u1ehi3]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        rcases p1577_3 (m.d 0 2) (by simp) with h1597 | h1597
                        · rcases p1577_3 (m.d 1 2) (by simp) with h1598 | h1598
                          · linarith only [h1224, h1598, hlam]
                          · linarith only [h1511, h1598, hlam]
                        · linarith only [h1597, h5, hlam]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h0, h1511, h1512, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1577_1, u1ehi3]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h5, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1511, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1571, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1573, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h6, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1511, hc25, hlam, hphi, ht12, p1577_1, u1ehi3]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [h1572, hlam, p1577_0]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        rcases p1577_3 (m.d 0 2) (by simp) with h1611 | h1611
                        · rcases p1577_3 (m.d 1 2) (by simp) with h1612 | h1612
                          · linarith only [h1512, h1612, hlam]
                          · linarith only [h1511, h1612, hlam]
                        · linarith only [h1611, h5, hlam]
                      · have p1577_0 := h1577c.1
                        have p1577_1 := h1577c.2.1
                        have p1577_2 := h1577c.2.2.1
                        have p1577_3 := h1577c.2.2.2
                        linarith only [hlam, p1577_0]
                · linarith only [h1224, h1511, h1568, h1572, hc13, hlam, hphi, u1ehi3]
              · linarith only [h1224, h1571, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1619 | h1619
            · linarith only [h1619, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1621 | h1621
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1622 | h1622
                · linarith only [h1224, h1511, h1568, h1622, hc23, hlam, hphi, ht12, u1ehi3]
                · linarith only [h1224, h1511, h1622, hc35, hlam, hphi, ht12, ht23, u1ehi3]
              · linarith only [h1224, h1511, h1621, hc34, hlam, hphi, ht12, ht23, u1ehi3]
        · linarith only [h1224, h1511, h1567, h7, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
    · linarith only [h1511, h5, h9, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8 h9

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 4 5 (by decide) (by decide) with h1628 | h1628
  · linarith only [h1628, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1630 | h1630
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1631 | h1631
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1632 | h1632
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1633 | h1633
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1634 | h1634
            · linarith only [h1, h1634, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1636 | h1636
              · linarith only [h1628, h1636, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1638 | h1638
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1639 | h1639
                  · linarith only [h1, h1630, h1639, h8, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1641 | h1641
                    · linarith only [h1628, h1631, h1641, h2, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1643 | h1643
                      · linarith only [h0, h1628, h1632, h1638, h1639, h1643, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                      · rcases h2bigk with h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c | h1645c
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, h1632, h1638, h1639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          rcases p1645_3 (m.d 0 2) (by simp) with h1648 | h1648
                          · rcases p1645_3 (m.d 1 2) (by simp) with h1649 | h1649
                            · linarith only [h0, h1649, hlam]
                            · linarith only [h1630, h1649, hlam]
                          · linarith only [h1648, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          rcases p1645_3 (m.d 0 2) (by simp) with h1653 | h1653
                          · rcases p1645_3 (m.d 1 2) (by simp) with h1654 | h1654
                            · linarith only [h0, h1654, hlam]
                            · linarith only [h1631, h1654, hlam]
                          · linarith only [h1653, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          rcases p1645_3 (m.d 0 2) (by simp) with h1658 | h1658
                          · rcases p1645_3 (m.d 1 2) (by simp) with h1659 | h1659
                            · linarith only [h0, h1659, hlam]
                            · linarith only [h1632, h1659, hlam]
                          · linarith only [h1658, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, hlam, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, h1638, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          rcases p1645_3 (m.d 0 2) (by simp) with h1666 | h1666
                          · rcases p1645_3 (m.d 1 2) (by simp) with h1667 | h1667
                            · rcases p1645_3 (m.d 2 3) (by simp) with h1668 | h1668
                              · linarith only [h1630, h1668, hlam]
                              · linarith only [h1638, h1668, hlam]
                            · linarith only [h1667, hlam, p1645_0]
                          · linarith only [h1666, h5, hlam]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, h1638, h1639, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h4, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1630, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1643, h4, h8, hc24, hc45, hlam, hphi, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1639, hlam, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h5, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1631, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1638, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1641, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h6, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h1632, hlam, p1645_0]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, h1632, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [h0, h1632, h1638, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1645_1]
                        · have p1645_0 := h1645c.1
                          have p1645_1 := h1645c.2.1
                          have p1645_2 := h1645c.2.2.1
                          have p1645_3 := h1645c.2.2.2
                          linarith only [hlam, p1645_0]
                · linarith only [h1638, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1633, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1691 | h1691
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1692 | h1692
            · linarith only [h1, h1692, h8, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1694 | h1694
              · linarith only [h1628, h1694, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1696 | h1696
                · linarith only [h0, h1630, h1632, h1696, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1696, h7, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1691, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1631, h5, h7, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h1630, h4, h8, hc35, hlam, hphi, ht12, ht23, u1ehi1]

set_option maxHeartbeats 6424000 in
theorem r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1ehi := hb1.1
  have h2bigk := hb2.1
  have h2emax := hb2.2.2
  have h4bigk := hb4.1
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8
  · exact r1l7_11_12_14_25_L_R_L_I_L_I_H_I_s3_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7 h8

end R2N4
