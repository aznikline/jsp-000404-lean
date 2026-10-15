import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1328 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1329 | h1329
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1330 | h1330
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1331 | h1331
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1332 | h1332
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1333 | h1333
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1334 | h1334
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1335 | h1335
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1336 | h1336
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1337 | h1337
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1338 | h1338
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1339 | h1339
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1341 | h1341
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1342 | h1342
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1343 | h1343
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1344 | h1344
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1345 | h1345
                                  · linarith only [h0, h1328, h1336, h1342, h1345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h1328, h1339, h1341, h1345, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h1328, h1339, h1341, h1344, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h1334, h1343, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1333, h1342, hc23, hlam, hphi, u3elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1351 | h1351
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1352 | h1352
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1353 | h1353
                                · linarith only [h1337, h1341, h1353, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1355 | h1355
                                  · linarith only [h1337, h1341, h1351, h1355, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                  · rcases h2bigk with h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c | h1357c
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h0, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h0, h1352, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1357_1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      rcases p1357_3 (m.d 0 2) (by simp) with h1361 | h1361
                                      · rcases p1357_3 (m.d 1 2) (by simp) with h1362 | h1362
                                        · rcases p1357_3 (m.d 2 3) (by simp) with h1363 | h1363
                                          · linarith only [h1330, h1363, hlam]
                                          · linarith only [h1351, h1363, hlam]
                                        · linarith only [h1337, h1362, hlam]
                                      · linarith only [h1361, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      rcases p1357_3 (m.d 0 2) (by simp) with h1368 | h1368
                                      · rcases p1357_3 (m.d 1 2) (by simp) with h1369 | h1369
                                        · rcases p1357_3 (m.d 2 3) (by simp) with h1370 | h1370
                                          · linarith only [h1330, h1370, hlam]
                                          · linarith only [h1352, h1370, hlam]
                                        · linarith only [h1338, h1369, hlam]
                                      · linarith only [h1368, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1357_1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1352, h1355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1357_1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      rcases p1357_3 (m.d 0 2) (by simp) with h1378 | h1378
                                      · linarith only [h0, h1378, hlam]
                                      · linarith only [h1331, h1378, hlam]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      rcases p1357_3 (m.d 0 2) (by simp) with h1381 | h1381
                                      · linarith only [h0, h1381, hlam]
                                      · linarith only [h1332, h1381, hlam]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1330, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1336, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1336, h1351, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1357_1, u3elo1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h0, h1328, h1336, h1352, h1355, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1357_1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1331, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1337, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1351, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1353, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1332, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1338, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1352, hlam, p1357_0]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [h1332, h1351, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1357_1]
                                    · have p1357_0 := h1357c.1
                                      have p1357_1 := h1357c.2.1
                                      have p1357_2 := h1357c.2.2.1
                                      have p1357_3 := h1357c.2.2.2
                                      linarith only [hlam, p1357_0]
                              · linarith only [h1334, h1352, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1333, h1351, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1334, h1340, hc13, hlam, hphi, u3elo0]
                      · linarith only [h1333, h1336, h1339, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h1332, h1338, hlam]
                  · linarith only [h0, h1331, h1337, hlam]
                · linarith only [h0, h1328, h1336, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1407 | h1407
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1408 | h1408
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1409 | h1409
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1410 | h1410
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1411 | h1411
                          · linarith only [h0, h1328, h1335, h1409, h1411, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1413 | h1413
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1414 | h1414
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1415 | h1415
                                · linarith only [h1331, h1335, h1415, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1417 | h1417
                                  · linarith only [h1333, h1335, h1417, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                                  · rcases h2bigk with h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c | h1419c
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h0, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h0, h1414, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      rcases p1419_3 (m.d 0 2) (by simp) with h1423 | h1423
                                      · rcases p1419_3 (m.d 1 2) (by simp) with h1424 | h1424
                                        · rcases p1419_3 (m.d 2 3) (by simp) with h1425 | h1425
                                          · linarith only [h1330, h1425, hlam]
                                          · linarith only [h1413, h1425, hlam]
                                        · linarith only [h1407, h1424, hlam]
                                      · linarith only [h1423, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      rcases p1419_3 (m.d 0 2) (by simp) with h1430 | h1430
                                      · rcases p1419_3 (m.d 1 2) (by simp) with h1431 | h1431
                                        · rcases p1419_3 (m.d 2 3) (by simp) with h1432 | h1432
                                          · linarith only [h1330, h1432, hlam]
                                          · linarith only [h1414, h1432, hlam]
                                        · linarith only [h1408, h1431, hlam]
                                      · linarith only [h1430, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1414, h1417, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      rcases p1419_3 (m.d 0 2) (by simp) with h1440 | h1440
                                      · linarith only [h0, h1440, hlam]
                                      · linarith only [h1331, h1440, hlam]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      rcases p1419_3 (m.d 0 2) (by simp) with h1443 | h1443
                                      · linarith only [h0, h1443, hlam]
                                      · linarith only [h1332, h1443, hlam]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1330, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1406, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1328, h1406, h1413, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h0, h1328, h1406, h1414, h1417, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1331, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1407, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1413, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1415, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1332, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1408, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h1414, hlam, p1419_0]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [h0, h1332, h1413, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1419_1]
                                    · have p1419_0 := h1419c.1
                                      have p1419_1 := h1419c.2.1
                                      have p1419_2 := h1419c.2.2.1
                                      have p1419_3 := h1419c.2.2.2
                                      linarith only [hlam, p1419_0]
                              · linarith only [h1334, h1414, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1333, h1413, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1334, h1410, hc13, hlam, hphi, u3elo0]
                      · linarith only [h1333, h1406, h1409, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h1332, h1408, hlam]
                  · linarith only [h0, h1331, h1407, hlam]
                · linarith only [h0, h1406, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1468 | h1468
              · linarith only [h1333, h1334, h1468, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1470 | h1470
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1471 | h1471
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1472 | h1472
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1473 | h1473
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1474 | h1474
                        · linarith only [h1328, h1334, h1474, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1476 | h1476
                          · linarith only [h0, h1329, h1468, h1473, h1474, h1476, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1478 | h1478
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1479 | h1479
                              · linarith only [h1328, h1334, h1470, h1479, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1481 | h1481
                                · linarith only [h1331, h1333, h1334, h1476, h1481, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1483 | h1483
                                  · linarith only [h1333, h1334, h1468, h1483, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                  · rcases h2bigk with h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h0, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h0, h1478, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      rcases p1485_3 (m.d 0 2) (by simp) with h1489 | h1489
                                      · rcases p1485_3 (m.d 1 2) (by simp) with h1490 | h1490
                                        · rcases p1485_3 (m.d 2 3) (by simp) with h1491 | h1491
                                          · linarith only [h1330, h1491, hlam]
                                          · linarith only [h1478, h1491, hlam]
                                        · linarith only [h1471, h1490, hlam]
                                      · linarith only [h1489, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h0, h1478, h1479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1478, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      rcases p1485_3 (m.d 0 2) (by simp) with h1500 | h1500
                                      · linarith only [h0, h1500, hlam]
                                      · linarith only [h1331, h1500, hlam]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1478, h1479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1330, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1470, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1478, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1485_1, u3elo2]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1479, hlam, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1331, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1471, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1478, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1481, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1332, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1472, hlam, p1485_0]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h1332, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [h0, h1329, h1472, h1478, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1485_1]
                                    · have p1485_0 := h1485c.1
                                      have p1485_1 := h1485c.2.1
                                      have p1485_2 := h1485c.2.2.1
                                      have p1485_3 := h1485c.2.2.2
                                      linarith only [hlam, p1485_0]
                            · linarith only [h1333, h1334, h1478, hc23, hlam, hphi, u3elo4]
                      · linarith only [h1333, h1470, h1473, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h1332, h1472, hlam]
                  · linarith only [h0, h1331, h1471, hlam]
                · linarith only [h0, h1470, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1524 | h1524
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1525 | h1525
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1526 | h1526
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1527 | h1527
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1528 | h1528
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1529 | h1529
                      · linarith only [h0, h1328, h1333, h1529, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1531 | h1531
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1532 | h1532
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1533 | h1533
                            · linarith only [h1328, h1333, h1526, h1533, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1535 | h1535
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1536 | h1536
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1537 | h1537
                                  · rcases h2bigk with h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c | h1538c
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h0, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h0, h1535, h1537, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h0, h1533, h1535, h1537, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      rcases p1538_3 (m.d 0 2) (by simp) with h1543 | h1543
                                      · rcases p1538_3 (m.d 1 2) (by simp) with h1544 | h1544
                                        · rcases p1538_3 (m.d 2 3) (by simp) with h1545 | h1545
                                          · linarith only [h1330, h1545, hlam]
                                          · linarith only [h1535, h1545, hlam]
                                        · linarith only [h1528, h1544, hlam]
                                      · linarith only [h1543, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1535, h1537, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1533, h1535, h1537, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      rcases p1538_3 (m.d 0 2) (by simp) with h1554 | h1554
                                      · linarith only [h0, h1554, hlam]
                                      · linarith only [h1332, h1554, hlam]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1330, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1526, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1533, hlam, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1328, h1333, h1526, h1535, h1537, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1538_1, u3elo3]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1331, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1527, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1331, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1331, h1333, h1535, h1537, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1538_1, u3elo3]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1332, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1528, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1535, hlam, p1538_0]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [h1536, hlam, p1538_1]
                                    · have p1538_0 := h1538c.1
                                      have p1538_1 := h1538c.2.1
                                      have p1538_2 := h1538c.2.2.1
                                      have p1538_3 := h1538c.2.2.2
                                      linarith only [hlam, p1538_0]
                                  · linarith only [h1333, h1525, h1537, hlam]
                                · linarith only [h1329, h1333, h1524, h1532, h1533, h1535, h1536, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                              · linarith only [h1333, h1524, h1535, hc23, hlam, hphi, u3elo3]
                          · linarith only [h1333, h1524, h1525, h1529, h1532, hc13, hlam, hphi, u3elo3]
                        · linarith only [h1333, h1524, h1526, h1531, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1332, h1528, hlam]
                  · linarith only [h0, h1331, h1527, hlam]
                · linarith only [h0, h1526, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1333, h1524, h1525, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1581 | h1581
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1582 | h1582
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1583 | h1583
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1584 | h1584
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1585 | h1585
                      · linarith only [h1333, h1585, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
                        · linarith only [h0, h1328, h1524, h1587, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1589 | h1589
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1590 | h1590
                            · linarith only [h1328, h1333, h1582, h1590, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1592 | h1592
                              · linarith only [h1328, h1524, h1582, h1592, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1594 | h1594
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1595 | h1595
                                  · rcases h2bigk with h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c | h1596c
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h0, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      rcases p1596_3 (m.d 0 2) (by simp) with h1599 | h1599
                                      · rcases p1596_3 (m.d 1 2) (by simp) with h1600 | h1600
                                        · rcases p1596_3 (m.d 2 3) (by simp) with h1601 | h1601
                                          · linarith only [h1601, hlam, p1596_0]
                                          · rcases p1596_3 (m.d 2 4) (by simp) with h1603 | h1603
                                            · linarith only [h1331, h1603, hlam]
                                            · linarith only [h1590, h1603, hlam]
                                        · linarith only [h1582, h1600, hlam]
                                      · linarith only [h1599, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h0, h1594, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      rcases p1596_3 (m.d 0 2) (by simp) with h1609 | h1609
                                      · rcases p1596_3 (m.d 1 2) (by simp) with h1610 | h1610
                                        · rcases p1596_3 (m.d 2 3) (by simp) with h1611 | h1611
                                          · linarith only [h1330, h1611, hlam]
                                          · rcases p1596_3 (m.d 2 4) (by simp) with h1613 | h1613
                                            · linarith only [h1331, h1613, hlam]
                                            · linarith only [h1594, h1613, hlam]
                                        · linarith only [h1584, h1610, hlam]
                                      · linarith only [h1609, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      rcases p1596_3 (m.d 0 2) (by simp) with h1620 | h1620
                                      · linarith only [h0, h1620, hlam]
                                      · linarith only [h1330, h1620, hlam]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1594, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      rcases p1596_3 (m.d 0 2) (by simp) with h1624 | h1624
                                      · linarith only [h0, h1624, hlam]
                                      · linarith only [h1332, h1624, hlam]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1330, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1582, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1590, hlam, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1592, hlam, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1331, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1583, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1331, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1331, h1333, h1592, hc23, hlam, hphi, p1596_1, u3elo3]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1332, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1584, hlam, p1596_0]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1329, h1584, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [h1594, hlam, p1596_1]
                                    · have p1596_0 := h1596c.1
                                      have p1596_1 := h1596c.2.1
                                      have p1596_2 := h1596c.2.2.1
                                      have p1596_3 := h1596c.2.2.2
                                      linarith only [hlam, p1596_0]
                                  · linarith only [h1331, h1333, h1594, h1595, hlam]
                                · linarith only [h1333, h1581, h1590, h1594, hc23, hlam, hphi, u3elo3]
                          · linarith only [h1333, h1581, h1582, h1585, h1589, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1329, h1332, h1584, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1331, h1583, hlam]
                · linarith only [h0, h1582, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1648 | h1648
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1649 | h1649
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1650 | h1650
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1651 | h1651
                      · linarith only [h0, h1328, h1333, h1651, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1653 | h1653
                        · linarith only [h1328, h1333, h1524, h1581, h1653, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1655 | h1655
                          · linarith only [h1333, h1581, h1651, h1655, hc03, hlam, hphi, u3elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1657 | h1657
                            · linarith only [h1328, h1333, h1648, h1657, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1659 | h1659
                              · linarith only [h1328, h1524, h1648, h1659, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1661 | h1661
                                · linarith only [h0, h1329, h1333, h1581, h1649, h1655, h1661, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1663 | h1663
                                  · linarith only [h1328, h1333, h1581, h1648, h1663, hc23, hlam, hphi, u3elo3]
                                  · rcases h2bigk with h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c | h1665c
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h0, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1668 | h1668
                                      · rcases p1665_3 (m.d 1 2) (by simp) with h1669 | h1669
                                        · rcases p1665_3 (m.d 2 3) (by simp) with h1670 | h1670
                                          · linarith only [h1670, hlam, p1665_0]
                                          · rcases p1665_3 (m.d 2 4) (by simp) with h1672 | h1672
                                            · linarith only [h1331, h1672, hlam]
                                            · linarith only [h1657, h1672, hlam]
                                        · linarith only [h1648, h1669, hlam]
                                      · linarith only [h1668, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1677 | h1677
                                      · rcases p1665_3 (m.d 1 2) (by simp) with h1678 | h1678
                                        · rcases p1665_3 (m.d 2 3) (by simp) with h1679 | h1679
                                          · linarith only [h1330, h1679, hlam]
                                          · rcases p1665_3 (m.d 2 4) (by simp) with h1681 | h1681
                                            · linarith only [h1681, hlam, p1665_0]
                                            · rcases p1665_3 (m.d 2 5) (by simp) with h1683 | h1683
                                              · linarith only [h1332, h1683, hlam]
                                              · linarith only [h1661, h1683, hlam]
                                        · linarith only [h1649, h1678, hlam]
                                      · linarith only [h1677, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1688 | h1688
                                      · rcases p1665_3 (m.d 1 2) (by simp) with h1689 | h1689
                                        · rcases p1665_3 (m.d 2 3) (by simp) with h1690 | h1690
                                          · linarith only [h1330, h1690, hlam]
                                          · rcases p1665_3 (m.d 2 4) (by simp) with h1692 | h1692
                                            · linarith only [h1331, h1692, hlam]
                                            · rcases p1665_3 (m.d 2 5) (by simp) with h1694 | h1694
                                              · linarith only [h1694, hlam, p1665_0]
                                              · rcases h2emin with h1696 | h1696 | h1696 | h1696 | h1696
                                                · rcases h5bigk with h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c | h1697c
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1524, h1648, h1653, hc23, hlam, hphi, p1697_1, u3elo4]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1524, h1659, hc23, hlam, hphi, p1697_1, u3elo4]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1524, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1581, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1329, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h0, h1329, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1697_1]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1653, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1655, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1332, hlam, p1697_1]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1650, hlam, p1697_1]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1659, hlam, p1697_1]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1661, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1328, h1524, h1648, hc23, hlam, hphi, p1697_1, u3elo4]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1648, h1653, hc23, hlam, hphi, p1697_1, u3elo4]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1659, hc23, hlam, hphi, p1697_1, u3elo4]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1663, hlam, p1697_0]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    rcases p1697_3 (m.d 0 5) (by simp) with h1718 | h1718
                                                    · linarith only [h1581, h1718, hlam]
                                                    · rcases p1697_3 (m.d 1 5) (by simp) with h1720 | h1720
                                                      · linarith only [h1655, h1720, hlam]
                                                      · rcases p1697_3 (m.d 2 5) (by simp) with h1722 | h1722
                                                        · linarith only [h1661, h1722, hlam]
                                                        · rcases p1697_3 (m.d 3 5) (by simp) with h1724 | h1724
                                                          · linarith only [h1663, h1724, hlam]
                                                          · linarith only [h1524, h1724, hlam]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    rcases p1697_3 (m.d 0 5) (by simp) with h1727 | h1727
                                                    · linarith only [h1581, h1727, hlam]
                                                    · linarith only [h1329, h1727, hlam]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    rcases p1697_3 (m.d 0 5) (by simp) with h1730 | h1730
                                                    · linarith only [h1581, h1730, hlam]
                                                    · linarith only [h1332, h1730, hlam]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [h1328, h1524, h1648, hc23, hc45, hlam, hphi, ht34, p1697_1]
                                                  · have p1697_0 := h1697c.1
                                                    have p1697_1 := h1697c.2.1
                                                    have p1697_2 := h1697c.2.2.1
                                                    have p1697_3 := h1697c.2.2.2
                                                    linarith only [hlam, p1697_0]
                                                · rcases h5bigk with h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c | h1735c
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1524, h1648, h1651, h1655, hc23, hlam, hphi, p1735_1, u3elo4]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1524, h1657, h1661, hc23, hlam, hphi, p1735_1, u3elo4]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1524, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1581, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1329, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h0, h1329, h1661, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1735_1]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1653, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1655, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1332, hlam, p1735_1]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1650, hlam, p1735_1]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1659, hlam, p1735_1]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1661, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1328, h1524, h1648, hc23, hlam, hphi, p1735_1, u3elo4]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1648, h1653, hc23, hlam, hphi, p1735_1, u3elo4]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1657, h1661, hc23, hlam, hphi, p1735_1, u3elo4]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1663, hlam, p1735_0]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    rcases p1735_3 (m.d 0 5) (by simp) with h1756 | h1756
                                                    · linarith only [h1581, h1756, hlam]
                                                    · rcases p1735_3 (m.d 1 5) (by simp) with h1758 | h1758
                                                      · linarith only [h1655, h1758, hlam]
                                                      · rcases p1735_3 (m.d 2 5) (by simp) with h1760 | h1760
                                                        · linarith only [h1661, h1760, hlam]
                                                        · rcases p1735_3 (m.d 3 5) (by simp) with h1762 | h1762
                                                          · linarith only [h1663, h1762, hlam]
                                                          · linarith only [h1524, h1762, hlam]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    rcases p1735_3 (m.d 0 5) (by simp) with h1765 | h1765
                                                    · linarith only [h1581, h1765, hlam]
                                                    · linarith only [h1329, h1765, hlam]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    rcases p1735_3 (m.d 0 5) (by simp) with h1768 | h1768
                                                    · linarith only [h1581, h1768, hlam]
                                                    · linarith only [h1332, h1768, hlam]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [h1328, h1524, h1648, hc23, hc45, hlam, hphi, ht34, p1735_1]
                                                  · have p1735_0 := h1735c.1
                                                    have p1735_1 := h1735c.2.1
                                                    have p1735_2 := h1735c.2.2.1
                                                    have p1735_3 := h1735c.2.2.2
                                                    linarith only [hlam, p1735_0]
                                                · linarith only [h0, h1657, h1661, h1696, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1665_1]
                                                · linarith only [h0, h1661, h1696, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1665_1]
                                                · linarith only [h0, h1696, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1665_1]
                                        · linarith only [h1650, h1689, hlam]
                                      · linarith only [h1688, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1780 | h1780
                                      · linarith only [h0, h1780, hlam]
                                      · linarith only [h1330, h1780, hlam]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1783 | h1783
                                      · linarith only [h0, h1783, hlam]
                                      · linarith only [h1331, h1783, hlam]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      rcases p1665_3 (m.d 0 2) (by simp) with h1786 | h1786
                                      · linarith only [h0, h1786, hlam]
                                      · linarith only [h1332, h1786, hlam]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1330, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1648, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1657, hlam, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1659, hlam, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1331, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1649, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1331, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1661, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1332, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h1650, hlam, p1665_0]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h0, h1332, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [h0, h1329, h1650, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1665_1]
                                    · have p1665_0 := h1665c.1
                                      have p1665_1 := h1665c.2.1
                                      have p1665_2 := h1665c.2.2.1
                                      have p1665_3 := h1665c.2.2.2
                                      linarith only [hlam, p1665_0]
                    · linarith only [h0, h1332, h1650, hlam]
                  · linarith only [h0, h1331, h1649, hlam]
                · linarith only [h0, h1648, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · linarith only [h0, h1329, h1332, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1808 | h1808
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1809 | h1809
          · linarith only [h0, h1328, h1331, h1809, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1811 | h1811
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1812 | h1812
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1813 | h1813
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1814 | h1814
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1815 | h1815
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                      · linarith only [h0, h1328, h1331, h1809, h1814, h1816, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1328, h1331, h1814, h1816, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1331, h1813, h1814, h1815, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1820 | h1820
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1821 | h1821
                      · linarith only [h0, h1328, h1814, h1821, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1328, h1814, h1821, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1808, h1813, h1820, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1813, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h0, h1328, h1331, h1811, h1812, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1827 | h1827
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1828 | h1828
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1829 | h1829
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1830 | h1830
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
                      · linarith only [h0, h1328, h1331, h1809, h1829, h1831, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1328, h1331, h1828, h1829, h1831, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1331, h1828, h1829, h1830, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1835 | h1835
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1836 | h1836
                      · linarith only [h0, h1328, h1331, h1809, h1829, h1836, hc02, hc24, hlam, hphi]
                      · linarith only [h0, h1328, h1828, h1829, h1836, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1808, h1828, h1835, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1328, h1828, hc13, hlam, hphi, u3elo2]
              · linarith only [h0, h1329, h1331, h1827, hlam]
        · linarith only [h0, h1329, h1808, hlam]
    · linarith only [h0, h1328, h1330, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1844 | h1844
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1845 | h1845
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1846 | h1846
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1847 | h1847
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1848 | h1848
            · linarith only [h1328, h1329, h1848, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1850 | h1850
              · linarith only [h1328, h1329, h1847, h1850, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1852 | h1852
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1853 | h1853
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1854 | h1854
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1855 | h1855
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1856 | h1856
                        · linarith only [h1328, h1329, h1848, h1854, h1856, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1328, h1329, h1856, hc13, hlam, hphi, u3elo4]
                      · linarith only [h1847, h1852, h1855, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h1328, h1846, h1852, h1854, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1845, h1853, hlam]
                · linarith only [h0, h1852, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1863 | h1863
            · linarith only [h1328, h1329, h1847, h1863, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1865 | h1865
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1866 | h1866
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1867 | h1867
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1868 | h1868
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1869 | h1869
                      · linarith only [h1328, h1329, h1847, h1868, h1869, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1871 | h1871
                        · linarith only [h1328, h1329, h1863, h1871, hlam]
                        · linarith only [h1328, h1329, h1866, h1871, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1846, h1868, hlam]
                  · linarith only [h0, h1845, h1867, hlam]
                · linarith only [h0, h1328, h1866, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1877 | h1877
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1878 | h1878
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1879 | h1879
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1880 | h1880
                      · linarith only [h1328, h1329, h1847, h1879, h1880, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1882 | h1882
                        · linarith only [h1328, h1329, h1863, h1882, hlam]
                        · linarith only [h1328, h1329, h1877, h1882, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1846, h1879, hlam]
                  · linarith only [h0, h1845, h1878, hlam]
                · linarith only [h0, h1877, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1888 | h1888
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1889 | h1889
            · linarith only [h1328, h1329, h1889, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1891 | h1891
              · linarith only [h0, h1328, h1846, h1888, h1891, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1893 | h1893
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1894 | h1894
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1895 | h1895
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1896 | h1896
                      · linarith only [h0, h1328, h1846, h1895, h1896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1888, h1889, h1896, hc13, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1899 | h1899
                      · linarith only [h0, h1328, h1895, h1899, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1888, h1889, h1899, hc13, hlam, hphi, u3elo4]
                  · linarith only [h0, h1845, h1846, h1891, h1894, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h1328, h1893, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1904 | h1904
            · linarith only [h1844, h1846, h1888, h1904, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1906 | h1906
              · linarith only [h1845, h1846, h1906, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1908 | h1908
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1909 | h1909
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1910 | h1910
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1911 | h1911
                      · linarith only [h0, h1328, h1846, h1888, h1910, h1911, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1913 | h1913
                        · linarith only [h0, h1328, h1846, h1904, h1913, hlam]
                        · linarith only [h1328, h1329, h1908, h1913, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1916 | h1916
                      · linarith only [h1888, h1916, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1918 | h1918
                        · linarith only [h0, h1328, h1846, h1904, h1910, h1918, hc02, hc25, hlam, hphi]
                        · linarith only [h0, h1328, h1908, h1910, h1918, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1328, h1845, h1908, h1909, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1908, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1923 | h1923
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1924 | h1924
          · linarith only [h0, h1328, h1845, h1924, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1926 | h1926
            · linarith only [h1328, h1329, h1926, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1928 | h1928
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1929 | h1929
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1930 | h1930
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1931 | h1931
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1932 | h1932
                      · linarith only [h1328, h1329, h1845, h1923, h1924, h1930, h1932, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1328, h1329, h1845, h1923, h1929, h1930, h1932, hc23, hlam, hphi, u3elo3]
                    · linarith only [h1845, h1923, h1930, h1931, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1936 | h1936
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1937 | h1937
                      · linarith only [h0, h1328, h1930, h1937, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1328, h1329, h1930, h1936, h1937, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1923, h1936, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1328, h1929, hc13, hlam, hphi, u3elo2]
              · linarith only [h1845, h1923, h1928, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1943 | h1943
          · linarith only [h0, h1328, h1845, h1943, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1945 | h1945
            · linarith only [h1844, h1923, h1943, h1945, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1947 | h1947
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1948 | h1948
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1949 | h1949
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1950 | h1950
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1951 | h1951
                      · linarith only [h0, h1328, h1923, h1943, h1950, h1951, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h1328, h1845, h1948, h1949, h1951, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1845, h1948, h1949, h1950, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1955 | h1955
                    · linarith only [h0, h1328, h1923, h1948, h1949, h1955, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1957 | h1957
                      · linarith only [h0, h1328, h1949, h1957, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1328, h1949, h1957, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h1328, h1948, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1961 | h1961
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1962 | h1962
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1963 | h1963
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1964 | h1964
                      · linarith only [h0, h1328, h1845, h1962, h1964, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1328, h1845, h1961, h1962, h1964, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h1328, h1845, h1961, h1962, h1963, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1968 | h1968
                    · linarith only [h0, h1328, h1923, h1961, h1962, h1968, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1970 | h1970
                      · linarith only [h0, h1328, h1845, h1947, h1970, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1328, h1962, h1970, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h1328, h1961, hc13, hlam, hphi, u3elo2]
    · linarith only [h0, h1328, h1844, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 6254000 in
set_option maxHeartbeats 6254000 in
theorem r1l7_22_13_15_H_I_L_0_L_I_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1328 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1976 | h1976
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1977 | h1977
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1978 | h1978
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1979 | h1979
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1980 | h1980
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1981 | h1981
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1982 | h1982
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1983 | h1983
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1984 | h1984
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1985 | h1985
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1986 | h1986
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1987 | h1987
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1988 | h1988
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1989 | h1989
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1990 | h1990
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1991 | h1991
                                · rcases h2bigk with h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c | h1992c
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h0, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1988, h1991, hc02, hc45, hlam, hphi, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h0, h1988, h1991, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    rcases p1992_3 (m.d 0 2) (by simp) with h1997 | h1997
                                    · rcases p1992_3 (m.d 1 2) (by simp) with h1998 | h1998
                                      · rcases p1992_3 (m.d 2 3) (by simp) with h1999 | h1999
                                        · linarith only [h1976, h1999, hlam]
                                        · linarith only [h1989, h1999, hlam]
                                      · linarith only [h1984, h1998, hlam]
                                    · linarith only [h1997, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1988, h1991, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1988, h1991, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    rcases p1992_3 (m.d 0 2) (by simp) with h2008 | h2008
                                    · linarith only [h0, h2008, hlam]
                                    · linarith only [h1978, h2008, hlam]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1976, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1982, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1976, h1988, h1991, hc02, hc45, hlam, hphi, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1328, h1976, h1989, h1991, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1992_1, u3elo1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1977, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1983, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1988, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h0, h1977, h1989, h1991, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1978, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1984, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1989, hlam, p1992_0]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [h1990, hlam, p1992_1]
                                  · have p1992_0 := h1992c.1
                                    have p1992_1 := h1992c.2.1
                                    have p1992_2 := h1992c.2.2.1
                                    have p1992_3 := h1992c.2.2.2
                                    linarith only [hlam, p1992_0]
                                · linarith only [h1328, h1975, h1987, h1991, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h1328, h1975, h1987, h1990, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1328, h1980, h1989, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h1979, h1988, hc23, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2030 | h2030
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2031 | h2031
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2032 | h2032
                              · linarith only [h1983, h1987, h2032, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2034 | h2034
                                · linarith only [h1987, h2030, h2034, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                                · rcases h2bigk with h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c | h2036c
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h0, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h0, h2030, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2036_1]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    rcases p2036_3 (m.d 0 2) (by simp) with h2040 | h2040
                                    · rcases p2036_3 (m.d 1 2) (by simp) with h2041 | h2041
                                      · rcases p2036_3 (m.d 2 3) (by simp) with h2042 | h2042
                                        · linarith only [h1976, h2042, hlam]
                                        · linarith only [h2030, h2042, hlam]
                                      · linarith only [h1983, h2041, hlam]
                                    · linarith only [h2040, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    rcases p2036_3 (m.d 0 2) (by simp) with h2047 | h2047
                                    · rcases p2036_3 (m.d 1 2) (by simp) with h2048 | h2048
                                      · rcases p2036_3 (m.d 2 3) (by simp) with h2049 | h2049
                                        · linarith only [h1976, h2049, hlam]
                                        · linarith only [h2031, h2049, hlam]
                                      · linarith only [h1984, h2048, hlam]
                                    · linarith only [h2047, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2036_1]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h2031, h2034, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2036_1]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    rcases p2036_3 (m.d 0 2) (by simp) with h2057 | h2057
                                    · linarith only [h0, h2057, hlam]
                                    · linarith only [h1977, h2057, hlam]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    rcases p2036_3 (m.d 0 2) (by simp) with h2060 | h2060
                                    · linarith only [h0, h2060, hlam]
                                    · linarith only [h1978, h2060, hlam]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1976, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1982, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo2]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1328, h1976, h2031, h2034, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2036_1, u3elo1]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1977, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1983, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h2030, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h2032, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1978, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1984, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h2031, hlam, p2036_0]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [h1978, h2030, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2036_1]
                                  · have p2036_0 := h2036c.1
                                    have p2036_1 := h2036c.2.1
                                    have p2036_2 := h2036c.2.2.1
                                    have p2036_3 := h2036c.2.2.2
                                    linarith only [hlam, p2036_0]
                            · linarith only [h1328, h1980, h2031, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h1979, h2030, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1328, h1986, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1328, h1979, h1985, hlam]
                  · linarith only [h0, h1978, h1984, hlam]
                · linarith only [h0, h1977, h1983, hlam]
              · linarith only [h0, h1982, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2086 | h2086
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2087 | h2087
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2088 | h2088
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2089 | h2089
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2090 | h2090
                        · linarith only [h1328, h1975, h1977, h1981, h2090, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2092 | h2092
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2093 | h2093
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2094 | h2094
                              · linarith only [h1977, h1981, h2094, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2096 | h2096
                                · linarith only [h1977, h1981, h2092, h2096, hlam]
                                · rcases h2bigk with h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c | h2098c
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h0, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2092, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2098_1]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    rcases p2098_3 (m.d 0 2) (by simp) with h2102 | h2102
                                    · rcases p2098_3 (m.d 1 2) (by simp) with h2103 | h2103
                                      · rcases p2098_3 (m.d 2 3) (by simp) with h2104 | h2104
                                        · linarith only [h1976, h2104, hlam]
                                        · linarith only [h2092, h2104, hlam]
                                      · linarith only [h2086, h2103, hlam]
                                    · linarith only [h2102, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    rcases p2098_3 (m.d 0 2) (by simp) with h2109 | h2109
                                    · rcases p2098_3 (m.d 1 2) (by simp) with h2110 | h2110
                                      · rcases p2098_3 (m.d 2 3) (by simp) with h2111 | h2111
                                        · linarith only [h1976, h2111, hlam]
                                        · linarith only [h2093, h2111, hlam]
                                      · linarith only [h2087, h2110, hlam]
                                    · linarith only [h2109, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p2098_1]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2093, h2096, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2098_1]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    rcases p2098_3 (m.d 0 2) (by simp) with h2119 | h2119
                                    · linarith only [h0, h2119, hlam]
                                    · linarith only [h1977, h2119, hlam]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    rcases p2098_3 (m.d 0 2) (by simp) with h2122 | h2122
                                    · linarith only [h0, h2122, hlam]
                                    · linarith only [h1978, h2122, hlam]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h1976, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2085, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2092, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2098_1, u3elo2]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h1328, h1976, h2093, h2096, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2098_1, u3elo1]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h1977, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2086, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2092, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2094, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h1978, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2087, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h2093, hlam, p2098_0]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [h1978, h2092, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2098_1]
                                  · have p2098_0 := h2098c.1
                                    have p2098_1 := h2098c.2.1
                                    have p2098_2 := h2098c.2.2.1
                                    have p2098_3 := h2098c.2.2.2
                                    linarith only [hlam, p2098_0]
                            · linarith only [h1328, h1980, h2093, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1328, h1979, h2092, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1328, h2089, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1328, h1975, h1979, h1981, h2088, hlam]
                  · linarith only [h0, h1975, h1978, h2087, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1977, h2086, hlam]
              · linarith only [h0, h2085, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1328, h1975, h1980, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2148 | h2148
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2149 | h2149
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2150 | h2150
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2151 | h2151
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2152 | h2152
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2153 | h2153
                    · linarith only [h1328, h1975, h1979, h2152, h2153, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1328, h1975, h2152, h2153, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h1978, h2152, hlam]
                · linarith only [h0, h1977, h2151, hlam]
              · linarith only [h0, h1976, h2150, hlam]
            · linarith only [h1328, h1975, h1979, h2149, hlam]
          · linarith only [h1328, h1975, h2148, hlam]
      · linarith only [h1328, h1975, h1976, h1978, hc23, hlam, hphi, u3elo1]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2162 | h2162
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2163 | h2163
        · linarith only [h1976, h1977, h2163, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2165 | h2165
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2166 | h2166
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2167 | h2167
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2168 | h2168
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2169 | h2169
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2170 | h2170
                    · linarith only [h1328, h1975, h2163, h2169, h2170, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1328, h1975, h2169, h2170, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1977, h2168, h2169, hc02, hc25, hlam, hphi]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2174 | h2174
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2175 | h2175
                    · linarith only [h1328, h1975, h2163, h2174, h2175, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                    · linarith only [h1328, h1975, h2174, h2175, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h1975, h2162, h2174, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1975, h2167, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h1975, h1977, h2166, hlam]
          · linarith only [h1328, h1975, h2165, hlam]
      · linarith only [h0, h1975, h2162, hlam]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2183 | h2183
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2184 | h2184
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2185 | h2185
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2186 | h2186
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2187 | h2187
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2188 | h2188
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2189 | h2189
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2190 | h2190
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2191 | h2191
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2192 | h2192
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2193 | h2193
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2194 | h2194
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2195 | h2195
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2196 | h2196
                              · linarith only [h1976, h2183, h2188, h2196, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h1976, h2183, h2187, h2188, h2194, h2196, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h0, h1976, h2195, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1976, h2194, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h1976, h2183, h2187, h2188, h2193, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1976, h2188, h2192, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h1976, h2188, h2191, hc01, hlam, hphi, ht12, ht23, u3elo3]
                  · linarith only [h0, h1976, h2188, h2190, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h1976, h2183, h2188, h2189, hc12, hlam, hphi, ht23, u3elo1]
              · linarith only [h0, h2188, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2207 | h2207
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2208 | h2208
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2209 | h2209
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2210 | h2210
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2211 | h2211
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2212 | h2212
                        · linarith only [h1328, h1975, h2185, h2187, h2212, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2214 | h2214
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2215 | h2215
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2216 | h2216
                              · linarith only [h2183, h2187, h2216, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2218 | h2218
                                · linarith only [h2183, h2187, h2214, h2218, hlam]
                                · rcases h2bigk with h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c | h2220c
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h0, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h1976, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h1976, h2207, h2214, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2220_1, u3elo1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h1976, h2207, h2214, h2216, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2220_1, u3elo1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h0, h1975, h2208, h2212, h2214, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2220_1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h1328, h1975, h1976, h2208, h2212, h2214, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2220_1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    rcases p2220_3 (m.d 0 2) (by simp) with h2229 | h2229
                                    · linarith only [h0, h2229, hlam]
                                    · linarith only [h2183, h2229, hlam]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    rcases p2220_3 (m.d 0 2) (by simp) with h2232 | h2232
                                    · linarith only [h0, h2232, hlam]
                                    · linarith only [h2184, h2232, hlam]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h0, h1975, h2208, h2212, h2214, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2220_1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2207, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2207, h2214, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2220_1, u3elo1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2207, h2214, h2216, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2220_1, u3elo1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2183, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2208, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2214, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2216, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2184, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2209, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2215, hlam, p2220_0]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [h2184, h2214, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p2220_1]
                                  · have p2220_0 := h2220c.1
                                    have p2220_1 := h2220c.2.1
                                    have p2220_2 := h2220c.2.2.1
                                    have p2220_3 := h2220c.2.2.2
                                    linarith only [hlam, p2220_0]
                            · linarith only [h0, h1975, h1976, h2208, h2212, h2214, h2215, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                          · linarith only [h0, h1976, h2214, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h1328, h1975, h2209, h2211, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                    · linarith only [h0, h1975, h1976, h2207, h2209, h2210, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h0, h1976, h2184, h2207, h2209, hc01, hlam, hphi, ht12, ht23, u3elo1]
                · linarith only [h1976, h2207, h2208, hc02, hc24, hlam, hphi]
              · linarith only [h0, h1975, h2207, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h1328, h1975, h2186, hlam]
        · linarith only [h1976, h2183, h2185, hlam]
      · linarith only [h0, h1975, h2184, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2260 | h2260
      · rcases m.htr 0 3 4 (by decide) (by decide) with h2261 | h2261
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2262 | h2262
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2263 | h2263
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2264 | h2264
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2265 | h2265
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2266 | h2266
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2267 | h2267
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2268 | h2268
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2269 | h2269
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2270 | h2270
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2271 | h2271
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2272 | h2272
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2273 | h2273
                                · rcases h2bigk with h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c | h2274c
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h1976, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2183, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2183, h2265, h2271, h2273, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h2266, h2271, h2273, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h1976, h2266, h2271, h2273, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h2183, h2266, h2271, h2273, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    rcases p2274_3 (m.d 0 2) (by simp) with h2284 | h2284
                                    · linarith only [h0, h2284, hlam]
                                    · linarith only [h2260, h2284, hlam]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h2266, h2271, h2273, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2264, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h2183, h2264, h2266, h2271, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2264, h2271, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h0, h1975, h2266, h2271, h2273, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2265, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2270, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2265, h2267, h2271, h2273, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2274_1, u3elo1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2260, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2266, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2271, hlam, p2274_0]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [h2272, hlam, p2274_1]
                                  · have p2274_0 := h2274c.1
                                    have p2274_1 := h2274c.2.1
                                    have p2274_2 := h2274c.2.2.1
                                    have p2274_3 := h2274c.2.2.2
                                    linarith only [hlam, p2274_0]
                                · linarith only [h1328, h1975, h2269, h2273, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h0, h1975, h2183, h2269, h2272, hlam]
                            · linarith only [h0, h1976, h2271, hc01, hlam, hphi, ht12, ht23, u3elo4]
                          · linarith only [h0, h1975, h1976, h2269, h2270, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                        · linarith only [h2183, h2263, h2265, h2269, hlam]
                      · linarith only [h0, h2183, h2265, h2267, h2268, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1976, h2261, h2264, h2267, hlam]
                  · linarith only [h1976, h2260, h2266, hc12, hc23, hlam, hphi]
                · linarith only [h0, h1976, h2264, h2265, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h1975, h2264, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h1975, h2183, h2263, hlam]
          · linarith only [h1328, h1975, h2262, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h2314 | h2314
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2315 | h2315
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2316 | h2316
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2317 | h2317
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2318 | h2318
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2319 | h2319
                    · linarith only [h0, h1976, h2261, h2319, hc01, hlam, hphi, ht12, ht23, u3elo1]
                    · linarith only [h1328, h1975, h2318, h2319, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h1976, h2316, h2318, hc02, hc25, hlam, hphi]
                · linarith only [h0, h1975, h1976, h2316, h2317, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · linarith only [h0, h1975, h2316, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h1975, h2183, h2315, hlam]
          · linarith only [h0, h1975, h1976, h2314, hlam]
      · linarith only [h0, h1975, h2260, hlam]

end R2N4
