import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_45S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1281 | h1281
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1282 | h1282
    · linarith only [h1, h1282, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1284 | h1284
      · linarith only [h0, h1, h1284, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1286 | h1286
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1287 | h1287
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
            · linarith only [h0, h1, h1284, h1288, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1290 | h1290
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1291 | h1291
                · linarith only [h0, h1, h1288, h1291, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1293 | h1293
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1294 | h1294
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1295 | h1295
                      · linarith only [h0, h1282, h1288, h1290, h1294, h1295, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h0, h1282, h1290, h1295, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h1, h1287, h1290, h1294, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h1290, h1293, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1300 | h1300
                · linarith only [h1281, h1290, h1300, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1302 | h1302
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1303 | h1303
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1304 | h1304
                      · linarith only [h1281, h1282, h1288, h1303, h1304, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1306 | h1306
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1307 | h1307
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1308 | h1308
                            · linarith only [h1281, h1282, h1290, h1304, h1308, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1310 | h1310
                              · linarith only [h1281, h1282, h1302, h1308, h1310, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h1bigk with h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c | h1312c
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1282, h1300, h1308, hc12, hc45, hlam, hphi, ht23, ht34, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1282, h1300, h1308, hc14, hc45, hlam, hphi, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1282, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h0, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1288, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1290, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1300, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h0, h1288, hc12, hc23, hlam, hphi, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  rcases p1312_3 (m.d 0 1) (by simp) with h1324 | h1324
                                  · linarith only [h1, h1324, hlam]
                                  · linarith only [h0, h1324, hlam]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  rcases p1312_3 (m.d 0 1) (by simp) with h1328 | h1328
                                  · linarith only [h1, h1328, hlam]
                                  · linarith only [h1281, h1328, hlam]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1288, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1312_1, u5ehi1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1281, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1, h1281, h1288, hc12, hc23, hlam, hphi, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1302, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1304, hlam, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1281, h1290, h1300, h1308, hc12, hc45, hlam, hphi, ht23, ht34, p1312_1]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  rcases p1312_3 (m.d 0 1) (by simp) with h1338 | h1338
                                  · linarith only [h1282, h1338, hlam]
                                  · linarith only [h0, h1338, hlam]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [h1303, hlam, p1312_0]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  rcases p1312_3 (m.d 0 1) (by simp) with h1342 | h1342
                                  · linarith only [h1282, h1342, hlam]
                                  · linarith only [h1281, h1342, hlam]
                                · have p1312_0 := h1312c.1
                                  have p1312_1 := h1312c.2.1
                                  have p1312_2 := h1312c.2.2.1
                                  have p1312_3 := h1312c.2.2.2
                                  linarith only [hlam, p1312_0]
                          · linarith only [h1, h1281, h1287, h1288, h1290, h1307, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h1, h1287, h1288, h1306, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                    · linarith only [h1, h1287, h1303, hlam]
                  · linarith only [h1, h1287, h1302, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1350 | h1350
            · linarith only [h0, h1, h1287, h1350, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1353 | h1353
                · linarith only [h0, h1353, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1355 | h1355
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1356 | h1356
                    · linarith only [h0, h1, h1287, h1350, h1356, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1352, h1356, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h1352, h1355, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1360 | h1360
                · linarith only [h1281, h1352, h1360, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1362 | h1362
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1363 | h1363
                    · linarith only [h1, h1281, h1287, h1350, h1352, h1363, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h1281, h1352, h1363, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1281, h1352, h1362, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h1281, h1286, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1368 | h1368
    · linarith only [h1, h1368, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1370 | h1370
      · linarith only [h0, h1, h1370, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1373 | h1373
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1374 | h1374
            · linarith only [h0, h1, h1370, h1374, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1376 | h1376
              · linarith only [h0, h1281, h1376, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1378 | h1378
                · linarith only [h0, h1, h1374, h1378, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1380 | h1380
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1381 | h1381
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1382 | h1382
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1383 | h1383
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1384 | h1384
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1385 | h1385
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                              · linarith only [h1372, h1386, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · rcases h1bigk with h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c | h1388c
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1368, h1374, h1380, h1382, hc12, hc23, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1281, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1368, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1374, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1376, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1378, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, h1374, hc12, hc23, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  rcases p1388_3 (m.d 0 1) (by simp) with h1400 | h1400
                                  · linarith only [h1, h1400, hlam]
                                  · linarith only [h0, h1400, hlam]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1374, h1382, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1388_1, u5ehi1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, h1368, h1374, hc12, hc23, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, h1376, hc12, hc24, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  rcases p1388_3 (m.d 0 1) (by simp) with h1407 | h1407
                                  · linarith only [h1281, h1407, hlam]
                                  · linarith only [h0, h1407, hlam]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1380, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, h1368, h1374, h1380, hc12, hc23, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h0, h1378, hc12, hc25, hlam, hphi, p1388_1]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  rcases p1388_3 (m.d 0 1) (by simp) with h1414 | h1414
                                  · linarith only [h1368, h1414, hlam]
                                  · linarith only [h0, h1414, hlam]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1381, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [h1382, hlam, p1388_0]
                                · have p1388_0 := h1388c.1
                                  have p1388_1 := h1388c.2.1
                                  have p1388_2 := h1388c.2.2.1
                                  have p1388_3 := h1388c.2.2.2
                                  linarith only [hlam, p1388_0]
                            · linarith only [h0, h1281, h1376, h1385, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h0, h1, h1374, h1384, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1374, h1380, h1382, h1383, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h0, h1281, h1382, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1, h1373, h1381, hlam]
                  · linarith only [h1, h1372, h1380, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1426 | h1426
            · linarith only [h0, h1, h1373, h1426, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1428 | h1428
              · linarith only [h0, h1281, h1428, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1430 | h1430
                · linarith only [h0, h1281, h1372, h1373, h1430, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1433 | h1433
                    · linarith only [h0, h1281, h1372, h1373, h1426, h1433, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h1433, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h1372, h1432, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1437 | h1437
          · linarith only [h1372, h1437, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1439 | h1439
            · linarith only [h0, h1, h1372, h1439, hc23, hc34, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1441 | h1441
              · linarith only [h0, h1281, h1441, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1443 | h1443
                · linarith only [h0, h1, h1372, h1443, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1445 | h1445
                  · linarith only [h0, h1, h1372, h1439, h1445, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1445, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x0 m hb1 hb3 hb5 h0 h1
  · exact r1l7_11_13_25_L_I_L_I_H_R_x0_x1 m hb1 hb3 hb5 h0 h1

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1449 | h1449
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1450 | h1450
    · linarith only [h0, h1450, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1452 | h1452
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1453 | h1453
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1454 | h1454
          · linarith only [h0, h1448, h1454, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1456 | h1456
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1457 | h1457
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1460 | h1460
                    · linarith only [h1448, h1450, h1454, h1458, h1460, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1462 | h1462
                      · linarith only [h1448, h1450, h1459, h1460, h1462, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1448, h1450, h1459, h1462, hc34, hc45, hlam, hphi]
                  · linarith only [h1453, h1454, h1456, h1459, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1466 | h1466
                  · linarith only [h0, h1448, h1458, h1466, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1448, h1453, h1458, h1466, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h0, h1449, h1457, hlam]
            · linarith only [h0, h1449, h1452, h1456, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1471 | h1471
          · linarith only [h1453, h1471, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1473 | h1473
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1474 | h1474
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1475 | h1475
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1476 | h1476
                  · linarith only [h1448, h1450, h1453, h1475, h1476, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1478 | h1478
                    · linarith only [h1448, h1450, h1471, h1478, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1480 | h1480
                      · linarith only [h1449, h1450, h1478, h1480, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1482 | h1482
                        · linarith only [h1452, h1453, h1482, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1484 | h1484
                          · linarith only [h1449, h1450, h1473, h1476, h1478, h1484, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1486 | h1486
                            · linarith only [h1450, h1474, h1480, h1486, hc01, hc12, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1488 | h1488
                              · linarith only [h1449, h1450, h1473, h1476, h1480, h1488, hc23, hc34, hlam, hphi]
                              · rcases h1bigk with h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h0, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1450, h1473, h1478, hc23, hc35, hlam, hphi, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1450, h1473, h1476, h1478, hc23, hc35, hlam, hphi, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1450, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 1) (by simp) with h1496 | h1496
                                  · linarith only [h1496, hlam, p1490_0]
                                  · rcases p1490_3 (m.d 1 2) (by simp) with h1498 | h1498
                                    · rcases p1490_3 (m.d 1 3) (by simp) with h1499 | h1499
                                      · linarith only [h1473, h1499, hlam]
                                      · rcases p1490_3 (m.d 1 4) (by simp) with h1501 | h1501
                                        · linarith only [h1474, h1501, hlam]
                                        · rcases p1490_3 (m.d 1 5) (by simp) with h1503 | h1503
                                          · linarith only [h1475, h1503, hlam]
                                          · linarith only [h1450, h1503, hlam]
                                    · linarith only [h1498, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 1) (by simp) with h1508 | h1508
                                  · linarith only [h0, h1508, hlam]
                                  · linarith only [h1448, h1508, hlam]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 1) (by simp) with h1511 | h1511
                                  · linarith only [h0, h1511, hlam]
                                  · linarith only [h1449, h1511, hlam]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1490_1, u5ehi1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1448, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1473, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1476, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1478, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1449, hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1474, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h0, h1449, h1473, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1480, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1449, h1478, h1488, hc14, hc45, hlam, hphi, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [h1475, hlam, p1490_1]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 1) (by simp) with h1527 | h1527
                                  · linarith only [h1450, h1527, hlam]
                                  · linarith only [h1448, h1527, hlam]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  rcases p1490_3 (m.d 0 1) (by simp) with h1530 | h1530
                                  · linarith only [h1450, h1530, hlam]
                                  · linarith only [h1449, h1530, hlam]
                                · have p1490_0 := h1490c.1
                                  have p1490_1 := h1490c.2.1
                                  have p1490_2 := h1490c.2.2.1
                                  have p1490_3 := h1490c.2.2.2
                                  linarith only [hlam, p1490_0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1534 | h1534
                  · linarith only [h0, h1448, h1475, h1534, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1536 | h1536
                    · linarith only [h0, h1449, h1475, h1534, h1536, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1538 | h1538
                      · linarith only [h0, h1449, h1475, h1538, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1540 | h1540
                        · linarith only [h1448, h1453, h1473, h1540, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1542 | h1542
                          · linarith only [h0, h1449, h1473, h1475, h1534, h1536, h1542, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                          · linarith only [h0, h1449, h1473, h1475, h1534, h1542, hc23, hc35, hlam, hphi]
              · linarith only [h0, h1449, h1474, hlam]
            · linarith only [h0, h1452, h1473, hlam]
      · linarith only [h0, h1448, h1452, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1548 | h1548
    · linarith only [h0, h1548, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1550 | h1550
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1551 | h1551
        · linarith only [h1448, h1449, h1551, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1553 | h1553
          · linarith only [h1551, h1553, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1555 | h1555
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1556 | h1556
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1557 | h1557
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1558 | h1558
                  · linarith only [h1448, h1449, h1551, h1556, h1558, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1560 | h1560
                    · linarith only [h1448, h1548, h1553, h1560, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1562 | h1562
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1563 | h1563
                        · linarith only [h1558, h1562, h1563, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1565 | h1565
                          · linarith only [h1448, h1548, h1555, h1560, h1565, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1567 | h1567
                            · linarith only [h1556, h1567, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1569 | h1569
                              · rcases h1bigk with h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c | h1570c
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h0, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1548, h1555, h1560, hc23, hc35, hlam, hphi, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1449, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1548, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  rcases p1570_3 (m.d 0 1) (by simp) with h1576 | h1576
                                  · linarith only [h1576, hlam, p1570_0]
                                  · rcases p1570_3 (m.d 1 2) (by simp) with h1578 | h1578
                                    · rcases p1570_3 (m.d 1 3) (by simp) with h1579 | h1579
                                      · linarith only [h1555, h1579, hlam]
                                      · rcases p1570_3 (m.d 1 4) (by simp) with h1581 | h1581
                                        · linarith only [h1556, h1581, hlam]
                                        · linarith only [h1449, h1581, hlam]
                                    · linarith only [h1578, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  rcases p1570_3 (m.d 0 1) (by simp) with h1586 | h1586
                                  · linarith only [h0, h1586, hlam]
                                  · linarith only [h1448, h1586, hlam]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1562, h1567, hc12, hlam, hphi, ht01, ht0b, ht5b, p1570_1, u5ehi2]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1570_1, u5ehi1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1448, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1555, hlam, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1558, hlam, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1560, hlam, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1448, h1558, hc13, hc34, hlam, hphi, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1556, hlam, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  rcases p1570_3 (m.d 0 1) (by simp) with h1598 | h1598
                                  · linarith only [h1449, h1598, hlam]
                                  · linarith only [h1448, h1598, hlam]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1448, h1548, h1555, h1558, hc23, hc34, hlam, hphi, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1448, h1555, h1560, h1569, hc23, hc34, hlam, hphi, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1557, hlam, p1570_1]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  rcases p1570_3 (m.d 0 1) (by simp) with h1605 | h1605
                                  · linarith only [h1548, h1605, hlam]
                                  · linarith only [h1448, h1605, hlam]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [h1562, hlam, p1570_0]
                                · have p1570_0 := h1570c.1
                                  have p1570_1 := h1570c.2.1
                                  have p1570_2 := h1570c.2.2.1
                                  have p1570_3 := h1570c.2.2.2
                                  linarith only [hlam, p1570_0]
                              · linarith only [h1558, h1562, h1569, hlam]
                      · linarith only [h1448, h1449, h1555, h1562, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1612 | h1612
                  · linarith only [h0, h1448, h1557, h1612, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1614 | h1614
                    · linarith only [h1448, h1449, h1556, h1557, h1614, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1616 | h1616
                      · linarith only [h1556, h1557, h1616, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                      · linarith only [h1448, h1449, h1555, h1616, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1619 | h1619
                · linarith only [h1556, h1619, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1621 | h1621
                  · linarith only [h0, h1448, h1556, h1621, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1623 | h1623
                    · linarith only [h0, h1448, h1556, h1623, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1625 | h1625
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
                        · linarith only [h1621, h1625, h1626, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · linarith only [h0, h1448, h1556, h1626, hc13, hc34, hlam, hphi]
                      · linarith only [h1448, h1449, h1555, h1625, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h1550, h1555, hlam]
      · linarith only [h0, h1448, h1550, hlam]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1633 | h1633
  · linarith only [h1448, h1633, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1635 | h1635
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1636 | h1636
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1637 | h1637
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1638 | h1638
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1639 | h1639
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1640 | h1640
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1641 | h1641
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1643 | h1643
                    · linarith only [h1632, h1633, h1638, h1642, h1643, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1645 | h1645
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1646 | h1646
                        · linarith only [h1635, h1646, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1648 | h1648
                          · linarith only [h1632, h1633, h1639, h1643, h1648, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1650 | h1650
                            · linarith only [h1633, h1637, h1643, h1645, h1646, h1650, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c | h1652c
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h0, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1448, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1633, h1639, h1643, h1645, hc34, hc45, hlam, hphi, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1633, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                rcases p1652_3 (m.d 0 1) (by simp) with h1658 | h1658
                                · linarith only [h1658, hlam, p1652_0]
                                · rcases p1652_3 (m.d 1 2) (by simp) with h1660 | h1660
                                  · rcases p1652_3 (m.d 1 3) (by simp) with h1661 | h1661
                                    · linarith only [h1638, h1661, hlam]
                                    · linarith only [h1448, h1661, hlam]
                                  · linarith only [h1660, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1448, h1637, h1646, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                rcases p1652_3 (m.d 0 1) (by simp) with h1667 | h1667
                                · linarith only [h0, h1667, hlam]
                                · linarith only [h1632, h1667, hlam]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1652_1, u5ehi1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                rcases p1652_3 (m.d 0 1) (by simp) with h1671 | h1671
                                · linarith only [h1671, hlam, p1652_0]
                                · rcases p1652_3 (m.d 1 2) (by simp) with h1673 | h1673
                                  · rcases p1652_3 (m.d 1 3) (by simp) with h1674 | h1674
                                    · rcases p1652_3 (m.d 1 4) (by simp) with h1675 | h1675
                                      · linarith only [h1641, h1675, hlam]
                                      · rcases p1652_3 (m.d 1 5) (by simp) with h1677 | h1677
                                        · linarith only [h1642, h1677, hlam]
                                        · linarith only [h1633, h1677, hlam]
                                    · linarith only [h1674, hlam, p1652_0]
                                  · linarith only [h0, h1673, hlam]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1638, hlam, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                rcases p1652_3 (m.d 0 1) (by simp) with h1684 | h1684
                                · linarith only [h1448, h1684, hlam]
                                · linarith only [h1632, h1684, hlam]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1633, h1638, hc01, hc12, hlam, hphi, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1632, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1639, hlam, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1641, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1643, hlam, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1632, h1639, h1643, h1645, hc34, hc45, hlam, hphi, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1640, hlam, p1652_1]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [h1642, hlam, p1652_0]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                rcases p1652_3 (m.d 0 1) (by simp) with h1696 | h1696
                                · linarith only [h1633, h1696, hlam]
                                · linarith only [h1632, h1696, hlam]
                              · have p1652_0 := h1652c.1
                                have p1652_1 := h1652c.2.1
                                have p1652_2 := h1652c.2.2.1
                                have p1652_3 := h1652c.2.2.2
                                linarith only [hlam, p1652_0]
                      · linarith only [h1632, h1633, h1641, h1643, h1645, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1448, h1632, h1637, h1642, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1448, h1637, h1641, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · linarith only [h0, h1635, h1637, h1640, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h1635, h1637, h1639, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · linarith only [h0, h1635, h1637, h1638, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1706 | h1706
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1707 | h1707
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1708 | h1708
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1709 | h1709
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1710 | h1710
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1711 | h1711
                    · linarith only [h1632, h1711, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1713 | h1713
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1714 | h1714
                        · linarith only [h1448, h1632, h1635, h1637, h1714, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1716 | h1716
                          · linarith only [h1448, h1632, h1637, h1707, h1710, h1711, h1716, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1718 | h1718
                            · linarith only [h1448, h1632, h1637, h1707, h1710, h1711, h1713, h1718, hlam]
                            · rcases h1bigk with h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c | h1720c
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h0, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, h1637, h1706, h1707, h1710, h1713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1633, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1726 | h1726
                                · linarith only [h1726, hlam, p1720_0]
                                · rcases p1720_3 (m.d 1 2) (by simp) with h1728 | h1728
                                  · rcases p1720_3 (m.d 1 3) (by simp) with h1729 | h1729
                                    · linarith only [h1706, h1729, hlam]
                                    · linarith only [h1448, h1729, hlam]
                                  · linarith only [h1728, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, h1637, h1710, hc01, hc12, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, h1632, h1637, h1706, h1710, hlam, p1720_2]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1632, h1633, h1707, h1713, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1737 | h1737
                                · linarith only [h1737, hlam, p1720_0]
                                · rcases p1720_3 (m.d 1 2) (by simp) with h1739 | h1739
                                  · rcases p1720_3 (m.d 1 3) (by simp) with h1740 | h1740
                                    · rcases p1720_3 (m.d 1 4) (by simp) with h1741 | h1741
                                      · linarith only [h1709, h1741, hlam]
                                      · rcases p1720_3 (m.d 1 5) (by simp) with h1743 | h1743
                                        · linarith only [h1710, h1743, hlam]
                                        · linarith only [h1633, h1743, hlam]
                                    · linarith only [h1740, hlam, p1720_0]
                                  · linarith only [h0, h1739, hlam]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1706, hlam, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, h1632, h1637, h1710, hlam, p1720_2]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1448, h1632, h1637, h1707, h1710, h1713, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1632, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1707, hlam, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1709, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1711, hlam, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1632, h1707, h1711, h1713, hc34, hc45, hlam, hphi, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1708, hlam, p1720_1]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [h1710, hlam, p1720_0]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                rcases p1720_3 (m.d 0 1) (by simp) with h1760 | h1760
                                · linarith only [h1633, h1760, hlam]
                                · linarith only [h1632, h1760, hlam]
                              · have p1720_0 := h1720c.1
                                have p1720_1 := h1720c.2.1
                                have p1720_2 := h1720c.2.2.1
                                have p1720_3 := h1720c.2.2.2
                                linarith only [hlam, p1720_0]
                      · linarith only [h1636, h1637, h1713, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1765 | h1765
                    · linarith only [h1448, h1632, h1710, h1765, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1767 | h1767
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1768 | h1768
                        · linarith only [h1448, h1710, h1768, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1770 | h1770
                          · linarith only [h1448, h1632, h1707, h1710, h1765, h1770, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1772 | h1772
                            · linarith only [h1448, h1632, h1707, h1710, h1765, h1767, h1772, hlam]
                            · linarith only [h1448, h1632, h1707, h1710, h1767, h1772, hc34, hc45, hlam, hphi]
                      · linarith only [h1448, h1636, h1710, h1767, hc23, hc35, hlam, hphi]
                · linarith only [h1448, h1632, h1636, h1709, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1777 | h1777
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1778 | h1778
                  · linarith only [h1706, h1708, h1778, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1780 | h1780
                    · linarith only [h1448, h1632, h1706, h1708, h1780, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1782 | h1782
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1783 | h1783
                        · linarith only [h1448, h1778, h1783, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1785 | h1785
                          · linarith only [h1448, h1632, h1706, h1707, h1708, h1780, h1785, hlam]
                          · linarith only [h1448, h1632, h1706, h1707, h1708, h1782, h1785, hc34, hc45, hlam, hphi]
                      · linarith only [h1636, h1637, h1782, hc23, hc35, hlam, hphi]
                · linarith only [h1448, h1636, h1637, h1777, hc01, hc35, hlam, hphi, ht12, ht23]
            · linarith only [h0, h1632, h1707, hlam]
          · linarith only [h0, h1632, h1635, h1706, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h1448, h1632, h1636, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1793 | h1793
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1795 | h1795
          · linarith only [h1635, h1794, h1795, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1798 | h1798
              · linarith only [h1795, h1798, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1802 | h1802
                    · linarith only [h1632, h1802, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1804 | h1804
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1805 | h1805
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1806 | h1806
                          · linarith only [h0, h1632, h1797, h1798, h1802, h1805, h1806, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                          · linarith only [h0, h1632, h1798, h1806, hc14, hc45, hlam, hphi]
                        · linarith only [h0, h1448, h1632, h1635, h1794, h1797, h1804, h1805, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1448, h1794, h1795, h1804, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                  · linarith only [h1448, h1794, h1801, hlam]
                · linarith only [h1448, h1794, h1800, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
            · linarith only [h0, h1632, h1797, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1814 | h1814
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1815 | h1815
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1816 | h1816
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1817 | h1817
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1818 | h1818
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1819 | h1819
                    · linarith only [h0, h1632, h1635, h1794, h1814, h1818, h1819, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1821 | h1821
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1822 | h1822
                        · linarith only [h0, h1635, h1794, h1814, h1822, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h1632, h1635, h1815, h1818, h1821, h1822, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1632, h1635, h1793, h1815, h1821, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1826 | h1826
                    · linarith only [h1632, h1826, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1828 | h1828
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1829 | h1829
                        · linarith only [h1814, h1818, h1829, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1831 | h1831
                          · linarith only [h0, h1632, h1635, h1814, h1815, h1818, h1826, h1831, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1833 | h1833
                            · linarith only [h0, h1632, h1635, h1814, h1815, h1818, h1826, h1828, h1833, hlam]
                            · linarith only [h0, h1632, h1635, h1814, h1815, h1818, h1828, h1833, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1632, h1635, h1793, h1815, h1828, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1448, h1632, h1793, h1817, hlam]
              · linarith only [h0, h1635, h1814, h1816, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h1632, h1635, h1814, h1815, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1840 | h1840
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1841 | h1841
              · linarith only [h1814, h1841, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1843 | h1843
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1844 | h1844
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1845 | h1845
                    · linarith only [h1632, h1845, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1847 | h1847
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1848 | h1848
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1849 | h1849
                          · linarith only [h0, h1632, h1635, h1794, h1814, h1840, h1841, h1844, h1845, h1849, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1632, h1840, h1841, h1847, h1849, hc34, hc45, hlam, hphi]
                        · linarith only [h1814, h1844, h1848, hlam]
                      · linarith only [h0, h1632, h1635, h1794, h1814, h1840, h1844, h1847, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1854 | h1854
                    · linarith only [h0, h1632, h1814, h1844, h1854, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1856 | h1856
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1857 | h1857
                        · linarith only [h0, h1632, h1814, h1840, h1844, h1856, h1857, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1632, h1814, h1840, h1856, h1857, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1632, h1814, h1840, h1856, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1632, h1793, h1814, h1840, h1843, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1632, h1840, hlam]
      · linarith only [h1448, h1632, h1793, hlam]

set_option maxHeartbeats 6098000 in
theorem r1l7_11_13_25_L_I_L_I_H_R_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1448 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1632 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1864 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h0, h1864, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]

end R2N4
