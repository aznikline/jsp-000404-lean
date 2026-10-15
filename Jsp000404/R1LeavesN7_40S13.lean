import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6854000 in
set_option maxHeartbeats 6854000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1315 | h1315
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1316 | h1316
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1317 | h1317
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1318 | h1318
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1319 | h1319
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1320 | h1320
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1321 | h1321
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1322 | h1322
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1323 | h1323
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1324 | h1324
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1325 | h1325
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1326 | h1326
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1327 | h1327
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1328 | h1328
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1329 | h1329
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1330 | h1330
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1331 | h1331
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1332 | h1332
                                    · linarith only [h1314, h1323, h1329, h1332, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h1315, h1324, h1331, h1332, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h1322, h1331, hc24, hlam, hphi, u4elo0]
                                · linarith only [h0, h1314, h1327, h1330, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · linarith only [h0, h1314, h1326, h1329, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1322, h1328, hc14, hlam, hphi, u4elo0]
                          · linarith only [h0, h1314, h1321, h1326, h1327, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
                          · linarith only [h0, h1314, h1320, h1326, h1340, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1342 | h1342
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1343 | h1343
                              · linarith only [h1317, h1326, h1343, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1345 | h1345
                                · linarith only [h1323, h1340, h1345, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1347 | h1347
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1348 | h1348
                                    · rcases h0bigk with h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h0, hlam, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h0, h1320, h1323, h1340, h1348, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h0, h1315, h1324, h1347, hc45, hlam, hphi, ht0b, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h0, h1321, h1323, h1340, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1314, h1323, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1320, h1323, h1340, h1348, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1320, h1323, h1340, h1348, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1321, h1323, h1340, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1314, hlam, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1317, hlam, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1314, h1320, h1323, h1340, h1348, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h0, h1314, h1321, h1323, h1340, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1315, hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1318, hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1320, hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1321, h1323, h1340, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1349_1, u0elo3]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1316, hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1319, hlam, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1321, hlam, p1349_0]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [h1322, hlam, p1349_1]
                                      · have p1349_0 := h1349c.1
                                        have p1349_1 := h1349c.2.1
                                        have p1349_2 := h1349c.2.2.1
                                        have p1349_3 := h1349c.2.2.2
                                        linarith only [hlam, p1349_0]
                                    · linarith only [h1324, h1347, h1348, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h1322, h1347, hc24, hlam, hphi, u4elo0]
                            · linarith only [h1322, h1342, hc14, hlam, hphi, u4elo0]
                      · linarith only [h0, h1319, h1325, hlam]
                    · linarith only [h0, h1324, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1317, h1323, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1381 | h1381
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1382 | h1382
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1383 | h1383
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1386 | h1386
                            · linarith only [h1315, h1322, h1386, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1388 | h1388
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1389 | h1389
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1390 | h1390
                                  · linarith only [h1315, h1322, h1382, h1390, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1392 | h1392
                                    · linarith only [h1314, h1322, h1381, h1388, h1392, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                    · rcases h0bigk with h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, h1314, h1381, h1389, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1398 | h1398
                                        · rcases p1394_3 (m.d 0 2) (by simp) with h1399 | h1399
                                          · rcases p1394_3 (m.d 0 3) (by simp) with h1400 | h1400
                                            · linarith only [h1314, h1400, hlam]
                                            · linarith only [h1320, h1400, hlam]
                                          · linarith only [h1318, h1399, hlam]
                                        · linarith only [h1315, h1398, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1405 | h1405
                                        · rcases p1394_3 (m.d 0 2) (by simp) with h1406 | h1406
                                          · rcases p1394_3 (m.d 0 3) (by simp) with h1407 | h1407
                                            · linarith only [h1314, h1407, hlam]
                                            · linarith only [h1321, h1407, hlam]
                                          · linarith only [h1319, h1406, hlam]
                                        · linarith only [h1316, h1405, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1314, h1381, h1389, h1392, hc34, hlam, hphi, ht0b, ht45, ht5b, p1394_1, u0elo1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1314, h1381, h1389, h1392, hc34, hlam, hphi, ht0b, ht45, ht5b, p1394_1, u0elo1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1415 | h1415
                                        · linarith only [h0, h1415, hlam]
                                        · linarith only [h1315, h1415, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1418 | h1418
                                        · linarith only [h0, h1418, hlam]
                                        · linarith only [h1316, h1418, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1314, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1317, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1424 | h1424
                                        · rcases p1394_3 (m.d 0 2) (by simp) with h1425 | h1425
                                          · rcases p1394_3 (m.d 0 3) (by simp) with h1426 | h1426
                                            · rcases p1394_3 (m.d 0 4) (by simp) with h1427 | h1427
                                              · linarith only [h1320, h1427, hlam]
                                              · rcases p1394_3 (m.d 0 5) (by simp) with h1429 | h1429
                                                · linarith only [h1321, h1429, hlam]
                                                · linarith only [h1322, h1429, hlam]
                                            · linarith only [h1320, h1426, hlam]
                                          · linarith only [h1318, h1425, hlam]
                                        · linarith only [h1315, h1424, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1435 | h1435
                                        · rcases p1394_3 (m.d 0 2) (by simp) with h1436 | h1436
                                          · rcases p1394_3 (m.d 0 3) (by simp) with h1437 | h1437
                                            · rcases p1394_3 (m.d 0 4) (by simp) with h1438 | h1438
                                              · linarith only [h1320, h1438, hlam]
                                              · rcases p1394_3 (m.d 0 5) (by simp) with h1440 | h1440
                                                · linarith only [h1321, h1440, hlam]
                                                · rcases h0emin with h1442 | h1442 | h1442 | h1442 | h1442
                                                  · rcases h1bigk with h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c | h1443c
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h0, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1381, h1389, h1392, hc34, hlam, hphi, ht0b, ht45, ht5b, p1443_1, u0elo0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      rcases p1443_3 (m.d 0 1) (by simp) with h1447 | h1447
                                                      · rcases p1443_3 (m.d 1 2) (by simp) with h1448 | h1448
                                                        · rcases p1443_3 (m.d 1 3) (by simp) with h1449 | h1449
                                                          · linarith only [h1314, h1449, hlam]
                                                          · linarith only [h1384, h1449, hlam]
                                                        · linarith only [h1382, h1448, hlam]
                                                      · linarith only [h1447, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      rcases p1443_3 (m.d 0 1) (by simp) with h1454 | h1454
                                                      · rcases p1443_3 (m.d 1 2) (by simp) with h1455 | h1455
                                                        · rcases p1443_3 (m.d 1 3) (by simp) with h1456 | h1456
                                                          · linarith only [h1314, h1456, hlam]
                                                          · linarith only [h1385, h1456, hlam]
                                                        · linarith only [h1383, h1455, hlam]
                                                      · linarith only [h1454, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1442, hc12, hlam, ht01, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      rcases p1443_3 (m.d 0 1) (by simp) with h1463 | h1463
                                                      · linarith only [h0, h1463, hlam]
                                                      · linarith only [h1314, h1463, hlam]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h0, h1314, h1315, h1322, hlam, p1394_1, p1443_2]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h0, h1314, h1316, hlam, p1394_1, p1443_2]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1314, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1381, hlam, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1314, h1382, h1388, hc34, hlam, hphi, ht0b, ht45, ht5b, p1443_1, u0elo0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h0, h1314, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1315, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1382, hlam, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1384, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1386, hlam, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1316, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1383, hlam, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h1385, hlam, p1443_0]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [h0, h1316, h1382, h1388, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1443_1]
                                                    · have p1443_0 := h1443c.1
                                                      have p1443_1 := h1443c.2.1
                                                      have p1443_2 := h1443c.2.2.1
                                                      have p1443_3 := h1443c.2.2.2
                                                      linarith only [hlam, p1443_0]
                                                  · rcases h1bigk with h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c | h1483c
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, h1381, h1389, h1392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      rcases p1483_3 (m.d 0 1) (by simp) with h1487 | h1487
                                                      · rcases p1483_3 (m.d 1 2) (by simp) with h1488 | h1488
                                                        · rcases p1483_3 (m.d 1 3) (by simp) with h1489 | h1489
                                                          · linarith only [h1314, h1489, hlam]
                                                          · linarith only [h1384, h1489, hlam]
                                                        · linarith only [h1382, h1488, hlam]
                                                      · linarith only [h1487, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      rcases p1483_3 (m.d 0 1) (by simp) with h1494 | h1494
                                                      · rcases p1483_3 (m.d 1 2) (by simp) with h1495 | h1495
                                                        · rcases p1483_3 (m.d 1 3) (by simp) with h1496 | h1496
                                                          · linarith only [h1314, h1496, hlam]
                                                          · linarith only [h1385, h1496, hlam]
                                                        · linarith only [h1383, h1495, hlam]
                                                      · linarith only [h1494, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1314, h1381, h1389, h1392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      rcases p1483_3 (m.d 0 1) (by simp) with h1503 | h1503
                                                      · linarith only [h0, h1503, hlam]
                                                      · linarith only [h1314, h1503, hlam]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, h1314, h1315, h1322, hlam, p1394_1, p1483_2]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, h1314, h1316, hlam, p1394_1, p1483_2]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1314, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1381, hlam, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1314, h1382, h1388, hc34, hlam, hphi, ht0b, ht45, ht5b, p1483_1, u0elo0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, h1314, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1315, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1382, hlam, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1384, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1386, hlam, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1316, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1383, hlam, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h1385, hlam, p1483_0]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [h0, h1316, h1382, h1388, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1483_1]
                                                    · have p1483_0 := h1483c.1
                                                      have p1483_1 := h1483c.2.1
                                                      have p1483_2 := h1483c.2.2.1
                                                      have p1483_3 := h1483c.2.2.2
                                                      linarith only [hlam, p1483_0]
                                                  · rcases h1bigk with h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c | h1523c
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, h1381, h1389, h1392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      rcases p1523_3 (m.d 0 1) (by simp) with h1527 | h1527
                                                      · rcases p1523_3 (m.d 1 2) (by simp) with h1528 | h1528
                                                        · rcases p1523_3 (m.d 1 3) (by simp) with h1529 | h1529
                                                          · linarith only [h1314, h1529, hlam]
                                                          · linarith only [h1384, h1529, hlam]
                                                        · linarith only [h1382, h1528, hlam]
                                                      · linarith only [h1527, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      rcases p1523_3 (m.d 0 1) (by simp) with h1534 | h1534
                                                      · rcases p1523_3 (m.d 1 2) (by simp) with h1535 | h1535
                                                        · rcases p1523_3 (m.d 1 3) (by simp) with h1536 | h1536
                                                          · linarith only [h1314, h1536, hlam]
                                                          · linarith only [h1385, h1536, hlam]
                                                        · linarith only [h1383, h1535, hlam]
                                                      · linarith only [h1534, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1314, h1381, h1389, h1392, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      rcases p1523_3 (m.d 0 1) (by simp) with h1543 | h1543
                                                      · linarith only [h0, h1543, hlam]
                                                      · linarith only [h1314, h1543, hlam]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, h1314, h1315, h1322, hlam, p1394_1, p1523_2]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, h1314, h1316, hlam, p1394_1, p1523_2]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1314, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1381, hlam, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1314, h1382, h1388, hc34, hlam, hphi, ht0b, ht45, ht5b, p1523_1, u0elo0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, h1314, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1315, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1382, hlam, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1384, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1386, hlam, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1316, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1383, hlam, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h1385, hlam, p1523_0]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [h0, h1316, h1382, h1388, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1523_1]
                                                    · have p1523_0 := h1523c.1
                                                      have p1523_1 := h1523c.2.1
                                                      have p1523_2 := h1523c.2.2.1
                                                      have p1523_3 := h1523c.2.2.2
                                                      linarith only [hlam, p1523_0]
                                                  · linarith only [h1322, h1442, hlam, p1394_1, u0elo2]
                                                  · linarith only [h1442, hlam, p1394_1, u0elo2]
                                            · linarith only [h1321, h1437, hlam]
                                          · linarith only [h1319, h1436, hlam]
                                        · linarith only [h1316, h1435, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1315, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1318, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1320, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1322, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1316, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1319, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1321, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1315, h1322, h1382, h1388, hc34, hlam, hphi, p1394_1, u4elo4]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                · linarith only [h0, h1314, h1385, h1389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h1320, h1322, h1388, hc23, hlam, hphi, ht34, u4elo4]
                          · linarith only [h0, h1314, h1321, h1384, h1385, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1320, h1322, h1384, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1319, h1383, hlam]
                    · linarith only [h0, h1382, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1317, h1381, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1585 | h1585
                · linarith only [h1320, h1321, h1585, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1587 | h1587
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1588 | h1588
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1589 | h1589
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1590 | h1590
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1591 | h1591
                          · linarith only [h1314, h1321, h1591, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1593 | h1593
                            · linarith only [h1585, h1593, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1595 | h1595
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1596 | h1596
                                · linarith only [h1314, h1321, h1587, h1596, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1598 | h1598
                                  · linarith only [h1314, h1315, h1321, h1585, h1587, h1588, h1595, h1598, hc34, hlam, hphi, u4elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1600 | h1600
                                    · linarith only [h1314, h1585, h1587, h1595, h1600, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · linarith only [h1314, h1321, h1587, h1595, h1600, hc34, hlam, hphi, u4elo4]
                              · linarith only [h1320, h1321, h1595, hc23, hc35, hlam, hphi]
                        · linarith only [h1320, h1321, h1587, h1590, hc23, hc35, hlam, hphi]
                      · linarith only [h0, h1319, h1589, hlam]
                    · linarith only [h0, h1314, h1587, h1588, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1317, h1587, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1608 | h1608
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1609 | h1609
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1610 | h1610
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1611 | h1611
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1612 | h1612
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1613 | h1613
                        · linarith only [h1314, h1320, h1613, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1615 | h1615
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1616 | h1616
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1617 | h1617
                              · linarith only [h1314, h1320, h1610, h1617, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1619 | h1619
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1620 | h1620
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1621 | h1621
                                    · rcases h0bigk with h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c | h1622c
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h0, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1314, h1610, h1619, h1621, hc45, hlam, hphi, ht0b, ht5b, p1622_1, u0elo0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h0, h1314, h1320, h1610, h1619, h1621, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        rcases p1622_3 (m.d 0 1) (by simp) with h1627 | h1627
                                        · rcases p1622_3 (m.d 0 2) (by simp) with h1628 | h1628
                                          · rcases p1622_3 (m.d 0 3) (by simp) with h1629 | h1629
                                            · linarith only [h1314, h1629, hlam]
                                            · linarith only [h1608, h1629, hlam]
                                          · linarith only [h1319, h1628, hlam]
                                        · linarith only [h1316, h1627, hlam]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1314, h1610, h1619, h1621, hc45, hlam, hphi, ht0b, ht5b, p1622_1, u0elo1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1314, h1610, h1619, h1621, hc45, hlam, hphi, ht0b, ht5b, p1622_1, u0elo1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1314, h1320, h1610, h1619, h1621, hc45, hlam, hphi, ht0b, ht5b, p1622_1, u0elo1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        rcases p1622_3 (m.d 0 1) (by simp) with h1638 | h1638
                                        · linarith only [h0, h1638, hlam]
                                        · linarith only [h1316, h1638, hlam]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1314, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1317, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1320, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1316, h1320, h1612, h1619, h1621, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1622_1, u4elo3]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1315, hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1318, hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht34, p1622_1, u4elo0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        rcases p1622_3 (m.d 0 1) (by simp) with h1650 | h1650
                                        · rcases p1622_3 (m.d 0 2) (by simp) with h1651 | h1651
                                          · rcases p1622_3 (m.d 0 3) (by simp) with h1652 | h1652
                                            · linarith only [h1320, h1652, hlam]
                                            · linarith only [h1608, h1652, hlam]
                                          · linarith only [h1319, h1651, hlam]
                                        · linarith only [h1316, h1650, hlam]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1316, hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1319, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1608, hlam, p1622_0]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [h1609, hlam, p1622_1]
                                      · have p1622_0 := h1622c.1
                                        have p1622_1 := h1622c.2.1
                                        have p1622_2 := h1622c.2.2.1
                                        have p1622_3 := h1622c.2.2.2
                                        linarith only [hlam, p1622_0]
                                    · linarith only [h1320, h1621, hc03, hlam, hphi, ht34, u4elo4]
                                  · linarith only [h1316, h1320, h1608, h1616, h1620, hc24, hlam, hphi, u4elo3]
                                · linarith only [h1320, h1608, h1619, hc23, hlam, hphi, ht34, u4elo3]
                            · linarith only [h1320, h1609, h1613, h1615, h1616, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h1320, h1608, h1615, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h1319, h1612, hlam]
                    · linarith only [h0, h1611, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1317, h1610, hlam]
                · linarith only [h1320, h1608, h1609, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1671 | h1671
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1672 | h1672
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1673 | h1673
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1674 | h1674
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1675 | h1675
                        · linarith only [h1314, h1320, h1675, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1677 | h1677
                          · linarith only [h1314, h1608, h1677, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1679 | h1679
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1680 | h1680
                              · linarith only [h1314, h1320, h1672, h1680, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1682 | h1682
                                · linarith only [h1314, h1608, h1672, h1682, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1684 | h1684
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1685 | h1685
                                    · rcases h0bigk with h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c | h1686c
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h0, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        rcases p1686_3 (m.d 0 1) (by simp) with h1689 | h1689
                                        · rcases p1686_3 (m.d 0 2) (by simp) with h1690 | h1690
                                          · rcases p1686_3 (m.d 0 3) (by simp) with h1691 | h1691
                                            · linarith only [h1314, h1691, hlam]
                                            · rcases p1686_3 (m.d 0 4) (by simp) with h1693 | h1693
                                              · linarith only [h1315, h1693, hlam]
                                              · linarith only [h1320, h1693, hlam]
                                          · linarith only [h1317, h1690, hlam]
                                        · linarith only [h1314, h1689, hlam]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h0, h1315, h1673, h1684, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        rcases p1686_3 (m.d 0 1) (by simp) with h1699 | h1699
                                        · rcases p1686_3 (m.d 0 2) (by simp) with h1700 | h1700
                                          · rcases p1686_3 (m.d 0 3) (by simp) with h1701 | h1701
                                            · linarith only [h1314, h1701, hlam]
                                            · rcases p1686_3 (m.d 0 4) (by simp) with h1703 | h1703
                                              · linarith only [h1315, h1703, hlam]
                                              · linarith only [h1671, h1703, hlam]
                                          · linarith only [h1319, h1700, hlam]
                                        · linarith only [h1316, h1699, hlam]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1314, h1672, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1686_1, u0elo1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        rcases p1686_3 (m.d 0 1) (by simp) with h1710 | h1710
                                        · linarith only [h0, h1710, hlam]
                                        · linarith only [h1314, h1710, hlam]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1315, h1673, h1684, hc45, hlam, hphi, ht0b, ht5b, p1686_1, u0elo1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        rcases p1686_3 (m.d 0 1) (by simp) with h1714 | h1714
                                        · linarith only [h0, h1714, hlam]
                                        · linarith only [h1316, h1714, hlam]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1314, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1317, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1320, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1608, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1315, hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1318, hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1314, h1672, hc23, hlam, hphi, ht34, p1686_1, u4elo0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1314, h1320, h1608, h1672, hc23, hlam, hphi, ht34, p1686_1, u4elo3]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1316, hlam, p1686_0]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1319, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1314, h1320, h1671, h1672, hc23, hlam, hphi, ht34, p1686_1, u4elo3]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [h1671, hlam, p1686_1]
                                      · have p1686_0 := h1686c.1
                                        have p1686_1 := h1686c.2.1
                                        have p1686_2 := h1686c.2.2.1
                                        have p1686_3 := h1686c.2.2.2
                                        linarith only [hlam, p1686_0]
                                    · linarith only [h1315, h1320, h1673, h1684, h1685, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                  · linarith only [h1315, h1679, h1680, h1684, hc23, hlam, hphi, ht34, u4elo0]
                            · linarith only [h1320, h1671, h1679, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1319, h1674, hlam]
                    · linarith only [h0, h1673, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1317, h1672, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1738 | h1738
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1739 | h1739
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1740 | h1740
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1741 | h1741
                        · linarith only [h1314, h1320, h1741, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1743 | h1743
                          · linarith only [h1608, h1741, h1743, hc03, hlam, hphi, ht34, u4elo1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
                            · linarith only [h1315, h1671, h1745, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1747 | h1747
                              · linarith only [h1314, h1320, h1738, h1747, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1749 | h1749
                                · linarith only [h1314, h1608, h1738, h1749, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1751 | h1751
                                  · linarith only [h1315, h1671, h1739, h1751, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1753 | h1753
                                    · linarith only [h1320, h1671, h1753, hc03, hlam, hphi, ht34, u4elo3]
                                    · linarith only [h1314, h1320, h1738, h1753, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1319, h1740, hlam]
                    · linarith only [h0, h1739, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1317, h1738, hlam]
          · linarith only [h0, h1316, h1319, hlam]
        · linarith only [h0, h1314, h1318, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1314, h1317, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1762 | h1762
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1763 | h1763
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1764 | h1764
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1765 | h1765
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1766 | h1766
              · linarith only [h1314, h1316, h1766, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1768 | h1768
                · linarith only [h1314, h1316, h1765, h1768, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1770 | h1770
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1771 | h1771
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1772 | h1772
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1773 | h1773
                        · linarith only [h1314, h1316, h1768, h1773, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1314, h1316, h1765, h1768, h1773, hc13, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1764, h1772, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1314, h1770, h1771, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1314, h1762, h1770, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1779 | h1779
              · linarith only [h1314, h1316, h1779, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1781 | h1781
                · linarith only [h1315, h1316, h1781, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1783 | h1783
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1784 | h1784
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1785 | h1785
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1786 | h1786
                        · linarith only [h1314, h1765, h1781, h1786, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1788 | h1788
                          · linarith only [h1314, h1316, h1779, h1788, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1790 | h1790
                            · linarith only [h1315, h1316, h1781, h1790, hlam]
                            · linarith only [h1315, h1316, h1783, h1786, h1790, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1764, h1785, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1314, h1783, h1784, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1762, h1783, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1796 | h1796
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1797 | h1797
              · linarith only [h0, h1314, h1764, h1797, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1799 | h1799
                · linarith only [h0, h1315, h1764, h1799, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1801 | h1801
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1802 | h1802
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1803 | h1803
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1804 | h1804
                        · linarith only [h0, h1314, h1764, h1803, h1804, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1314, h1764, h1796, h1803, h1804, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1807 | h1807
                        · linarith only [h0, h1314, h1803, h1807, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1314, h1796, h1801, h1803, h1807, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1802, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1314, h1762, h1796, h1801, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1812 | h1812
              · linarith only [h1314, h1316, h1812, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1814 | h1814
                · linarith only [h0, h1315, h1764, h1814, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1816 | h1816
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1817 | h1817
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1818 | h1818
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1819 | h1819
                        · linarith only [h0, h1314, h1764, h1818, h1819, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1821 | h1821
                          · linarith only [h0, h1315, h1764, h1812, h1819, h1821, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1823 | h1823
                            · linarith only [h0, h1315, h1764, h1814, h1823, hlam]
                            · linarith only [h1315, h1316, h1816, h1819, h1823, hc23, hlam, hphi, ht34, u4elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1826 | h1826
                        · linarith only [h0, h1314, h1796, h1818, h1826, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1828 | h1828
                          · linarith only [h1314, h1764, h1796, h1812, h1828, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1830 | h1830
                            · linarith only [h0, h1315, h1796, h1814, h1818, h1830, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · linarith only [h0, h1315, h1818, h1830, hc14, hlam, hphi, u4elo4]
                    · linarith only [h0, h1314, h1816, h1817, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1314, h1762, h1816, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1762, h1763, hc23, hlam, hphi, ht34, u4elo2]
      · linarith only [h0, h1314, h1762, hlam]
  · linarith only [h1314, h1315, hc13, hlam, hphi, ht34, u4elo1]

end R2N4
