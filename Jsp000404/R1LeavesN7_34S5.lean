import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6308000 in
set_option maxHeartbeats 6308000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h3bigk := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h1265 | h1265
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1266 | h1266
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1267 | h1267
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1268 | h1268
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1269 | h1269
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1270 | h1270
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1271 | h1271
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1272 | h1272
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1275 | h1275
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1276 | h1276
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1277 | h1277
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1278 | h1278
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1279 | h1279
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1280 | h1280
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1281 | h1281
                                  · linarith only [h0, h1265, h1273, h1278, h1281, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h1265, h1275, h1277, h1281, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h1265, h1275, h1277, h1280, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h1265, h1271, h1279, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h1265, h1270, h1278, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h1265, h1270, h1272, h1274, h1277, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · linarith only [h0, h1265, h1271, h1275, h1276, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1265, h1270, h1273, h1275, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1265, h1273, h1274, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1265, h1267, h1273, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1293 | h1293
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1294 | h1294
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1295 | h1295
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1296 | h1296
                          · linarith only [h0, h1265, h1272, h1294, h1296, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1298 | h1298
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1299 | h1299
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1300 | h1300
                                · linarith only [h1268, h1272, h1300, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1302 | h1302
                                  · linarith only [h0, h1265, h1272, h1292, h1298, h1302, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, hlam, p1304_1]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1265, h1292, h1299, h1302, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1304_1]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1266, h1293, h1296, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1265, h1293, h1295, h1296, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      rcases p1304_3 (m.d 0 1) (by simp) with h1312 | h1312
                                      · linarith only [h0, h1312, hlam]
                                      · linarith only [h1265, h1312, hlam]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      rcases p1304_3 (m.d 0 1) (by simp) with h1315 | h1315
                                      · linarith only [h0, h1315, hlam]
                                      · linarith only [h1265, h1272, h1293, h1295, h1296, h1315, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      rcases p1304_3 (m.d 0 1) (by simp) with h1318 | h1318
                                      · linarith only [h0, h1318, hlam]
                                      · linarith only [h1266, h1318, hlam]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1265, hlam, p1304_1]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1267, hlam, p1304_1]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1265, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1265, h1266, h1293, h1296, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1265, h1293, h1295, h1296, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1268, hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1270, hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1272, hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1266, hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1269, hlam, p1304_1]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h1271, hlam, p1304_0]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [h0, h1266, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1304_1, u2ehi3]
                                    · have p1304_0 := h1304c.1
                                      have p1304_1 := h1304c.2.1
                                      have p1304_2 := h1304c.2.2.1
                                      have p1304_3 := h1304c.2.2.2
                                      linarith only [hlam, p1304_0]
                              · linarith only [h0, h1265, h1271, h1298, h1299, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h1265, h1270, h1298, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h1265, h1271, h1294, h1295, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1265, h1270, h1292, h1294, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1265, h1292, h1293, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1265, h1267, h1268, h1271, h1272, h1292, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1342 | h1342
                · linarith only [h1270, h1271, h1342, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1344 | h1344
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1345 | h1345
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1346 | h1346
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1347 | h1347
                        · linarith only [h1265, h1271, h1347, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1349 | h1349
                          · linarith only [h1266, h1268, h1342, h1346, h1347, h1349, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1351 | h1351
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1352 | h1352
                              · linarith only [h1265, h1271, h1345, h1346, h1352, hc23, hlam, hphi, u2ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1354 | h1354
                                · linarith only [h1268, h1342, h1354, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                                  · linarith only [h0, h1266, h1268, h1342, h1344, h1347, h1351, h1356, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h0bigk with h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, hlam, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1265, h1344, h1351, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1265, h1271, h1345, h1346, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1265, h1345, h1346, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      rcases p1358_3 (m.d 0 1) (by simp) with h1366 | h1366
                                      · linarith only [h0, h1366, hlam]
                                      · linarith only [h1265, h1366, hlam]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      rcases p1358_3 (m.d 0 1) (by simp) with h1369 | h1369
                                      · linarith only [h0, h1369, hlam]
                                      · linarith only [h0, h1266, h1345, h1346, h1347, h1369, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      rcases p1358_3 (m.d 0 1) (by simp) with h1372 | h1372
                                      · linarith only [h0, h1372, hlam]
                                      · linarith only [h1266, h1372, hlam]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1265, hlam, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1267, hlam, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1271, h1356, hc04, hc45, hlam, hphi, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1271, hlam, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1266, h1345, h1346, h1347, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1268, hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1270, hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1342, hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1266, hlam, p1358_0]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h1269, hlam, p1358_1]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1265, h1266, h1345, h1346, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [h0, h1266, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1358_1, u2ehi3]
                                    · have p1358_0 := h1358c.1
                                      have p1358_1 := h1358c.2.1
                                      have p1358_2 := h1358c.2.2.1
                                      have p1358_3 := h1358c.2.2.2
                                      linarith only [hlam, p1358_0]
                            · linarith only [h0, h1265, h1270, h1351, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h1270, h1271, h1346, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1265, h1344, h1345, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1266, h1267, h1271, h1344, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1394 | h1394
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1395 | h1395
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1396 | h1396
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1397 | h1397
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1398 | h1398
                      · linarith only [h0, h1265, h1270, h1398, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1400 | h1400
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1401 | h1401
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1402 | h1402
                            · linarith only [h1265, h1270, h1396, h1402, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1404 | h1404
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1405 | h1405
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1406 | h1406
                                  · rcases h0bigk with h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c | h1407c
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h0, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h0, h1265, h1396, h1404, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h0, h1268, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1407_1, u2ehi3]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h0, h1269, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h0, h1265, h1396, h1404, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      rcases p1407_3 (m.d 0 1) (by simp) with h1415 | h1415
                                      · linarith only [h0, h1415, hlam]
                                      · linarith only [h1265, h1415, hlam]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      rcases p1407_3 (m.d 0 1) (by simp) with h1418 | h1418
                                      · linarith only [h0, h1418, hlam]
                                      · linarith only [h0, h1265, h1396, h1404, h1418, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      rcases p1407_3 (m.d 0 1) (by simp) with h1421 | h1421
                                      · linarith only [h0, h1421, hlam]
                                      · linarith only [h1266, h1421, hlam]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1265, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1267, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1270, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1269, h1270, hc34, hlam, hphi, ht23, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1265, h1270, h1396, h1404, hc34, hlam, hphi, ht23, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1268, hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1265, h1270, h1396, h1404, hc34, hlam, hphi, ht23, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1269, h1270, hc34, hlam, hphi, ht23, p1407_1, u2ehi4]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1266, hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1269, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1394, hlam, p1407_0]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [h1395, hlam, p1407_1]
                                    · have p1407_0 := h1407c.1
                                      have p1407_1 := h1407c.2.1
                                      have p1407_2 := h1407c.2.2.1
                                      have p1407_3 := h1407c.2.2.2
                                      linarith only [hlam, p1407_0]
                                  · linarith only [h1265, h1270, h1396, h1404, h1406, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · linarith only [h0, h1266, h1401, h1402, h1404, h1405, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h1270, h1394, h1404, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h1270, h1395, h1397, h1401, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1270, h1394, h1396, h1400, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1265, h1396, h1397, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1268, h1396, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1270, h1394, h1395, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1447 | h1447
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1448 | h1448
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1449 | h1449
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1450 | h1450
                      · linarith only [h1265, h1270, h1450, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1452 | h1452
                        · linarith only [h1265, h1394, h1452, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1454 | h1454
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1455 | h1455
                            · linarith only [h1265, h1270, h1448, h1455, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1457 | h1457
                              · linarith only [h1265, h1394, h1448, h1457, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1459 | h1459
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1460 | h1460
                                  · rcases h0bigk with h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c | h1461c
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h0, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h0, h1265, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h0, h1265, h1394, h1447, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h0, h1265, h1394, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1265, h1448, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      rcases p1461_3 (m.d 0 1) (by simp) with h1469 | h1469
                                      · linarith only [h0, h1469, hlam]
                                      · linarith only [h1265, h1469, hlam]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      rcases p1461_3 (m.d 0 1) (by simp) with h1472 | h1472
                                      · linarith only [h0, h1472, hlam]
                                      · linarith only [h0, h1266, h1448, h1452, h1472, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      rcases p1461_3 (m.d 0 1) (by simp) with h1475 | h1475
                                      · linarith only [h0, h1475, hlam]
                                      · linarith only [h1266, h1475, hlam]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1265, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1267, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1270, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1394, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1266, h1448, h1452, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1268, hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1265, h1270, h1448, hc34, hlam, hphi, ht23, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1269, h1270, hc34, hlam, hphi, ht23, p1461_1, u2ehi4]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1266, hlam, p1461_0]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1269, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h0, h1265, h1266, h1448, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1461_1, u2ehi2]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [h1447, hlam, p1461_1]
                                    · have p1461_0 := h1461c.1
                                      have p1461_1 := h1461c.2.1
                                      have p1461_2 := h1461c.2.2.1
                                      have p1461_3 := h1461c.2.2.2
                                      linarith only [hlam, p1461_0]
                                  · linarith only [h1265, h1270, h1448, h1460, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h1270, h1447, h1459, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1270, h1447, h1449, h1454, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h1266, h1269, h1449, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h1266, h1267, h1394, h1448, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1499 | h1499
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1500 | h1500
                      · linarith only [h0, h1265, h1270, h1500, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1502 | h1502
                        · linarith only [h1265, h1394, h1502, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1504 | h1504
                          · linarith only [h1265, h1270, h1447, h1498, h1500, h1504, hc34, hlam, hphi, ht23, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1506 | h1506
                            · linarith only [h1265, h1270, h1498, h1506, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1508 | h1508
                              · linarith only [h0, h1266, h1269, h1394, h1498, h1500, h1504, h1508, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1510 | h1510
                                · linarith only [h1265, h1270, h1447, h1498, h1510, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1512 | h1512
                                  · linarith only [h1265, h1270, h1447, h1498, h1512, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1265, h1270, h1498, h1512, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h1265, h1498, h1499, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1266, h1268, h1447, h1498, hc23, hlam, hphi, u2ehi3]
          · linarith only [h1267, h1269, hc25, hlam, hphi, u2ehi2]
        · linarith only [h1267, h1268, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1265, h1267, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1520 | h1520
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1521 | h1521
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1522 | h1522
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1523 | h1523
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1524 | h1524
              · linarith only [h1265, h1266, h1524, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
                · linarith only [h1265, h1266, h1523, h1526, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1528 | h1528
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1529 | h1529
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1530 | h1530
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1531 | h1531
                        · linarith only [h1265, h1266, h1524, h1531, hlam]
                        · linarith only [h1265, h1266, h1529, h1530, h1531, hc35, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h1523, h1524, h1530, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h1522, h1529, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h1522, h1528, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1537 | h1537
              · linarith only [h1265, h1266, h1537, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
                      · linarith only [h0, h1265, h1523, h1542, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1544 | h1544
                        · linarith only [h1265, h1266, h1537, h1544, hlam]
                        · linarith only [h1265, h1266, h1540, h1544, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1265, h1540, h1541, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1521, h1540, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1549 | h1549
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1550 | h1550
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1551 | h1551
                      · linarith only [h1265, h1523, h1551, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1553 | h1553
                        · linarith only [h1265, h1537, h1553, hlam]
                        · linarith only [h1265, h1266, h1549, h1553, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h0, h1265, h1549, h1550, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1521, h1549, hc23, hlam, hphi, u2ehi3]
          · linarith only [h1520, h1522, hc25, hlam, hphi, u2ehi2]
        · linarith only [h1520, h1521, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1265, h1520, hlam]
  · exact r1l7_10_12_23_L_I_L_R_H_I_s1 m hb0 hb2 hb3 h0 h1265

end R2N4
