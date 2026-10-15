import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1420 | h1420
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1421 | h1421
    · linarith only [h0, h1, h1421, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1423 | h1423
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1424 | h1424
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1425 | h1425
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1426 | h1426
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1427 | h1427
              · linarith only [h0, h1, h1421, h1427, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1429 | h1429
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1430 | h1430
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1431 | h1431
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1432 | h1432
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1433 | h1433
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1434 | h1434
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1435 | h1435
                            · linarith only [h0, h1, h1427, h1429, h1435, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h1420, h1432, h1435, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h1, h1427, h1434, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1427, h1433, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1426, h1432, hc14, hlam, hphi, u4elo0]
                    · linarith only [h0, h1, h1431, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h1429, h1430, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h1423, h1427, h1429, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1444 | h1444
              · linarith only [h0, h1, h1421, h1444, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1446 | h1446
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1449 | h1449
                      · linarith only [h1426, h1449, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1451 | h1451
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1452 | h1452
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1453 | h1453
                            · linarith only [h1420, h1426, h1446, h1453, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1455 | h1455
                              · linarith only [h1420, h1426, h1446, h1451, h1455, hlam]
                              · rcases h2bigk with h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c | h1457c
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, h1, h1444, h1446, h1451, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1421, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  rcases p1457_3 (m.d 0 2) (by simp) with h1461 | h1461
                                  · rcases p1457_3 (m.d 1 2) (by simp) with h1462 | h1462
                                    · linarith only [h0, h1462, hlam]
                                    · linarith only [h1446, h1462, hlam]
                                  · linarith only [h1461, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  rcases p1457_3 (m.d 0 2) (by simp) with h1466 | h1466
                                  · rcases p1457_3 (m.d 1 2) (by simp) with h1467 | h1467
                                    · linarith only [h0, h1467, hlam]
                                    · linarith only [h0, h1, h1444, h1446, h1451, h1467, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1457_1]
                                  · linarith only [h1466, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, hlam, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1444, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, h1, h1444, h1451, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, h1, h1444, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  rcases p1457_3 (m.d 0 2) (by simp) with h1476 | h1476
                                  · linarith only [h1476, hlam, p1457_0]
                                  · rcases p1457_3 (m.d 1 2) (by simp) with h1478 | h1478
                                    · linarith only [h1444, h1478, hlam]
                                    · rcases p1457_3 (m.d 2 3) (by simp) with h1480 | h1480
                                      · rcases p1457_3 (m.d 2 4) (by simp) with h1481 | h1481
                                        · linarith only [h1451, h1481, hlam]
                                        · rcases p1457_3 (m.d 2 5) (by simp) with h1483 | h1483
                                          · linarith only [h1452, h1483, hlam]
                                          · rcases h4bigk with h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c | h1485c
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1426, h1446, h1451, hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1426, h1451, hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1426, hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1426, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1420, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1451, hc34, hlam, hphi, p1485_1, u4elo1]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1420, h1426, hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1449, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1423, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1446, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hc34, hlam, hphi, p1485_1, u4elo2]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1453, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1425, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1447, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1451, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1455, hlam, p1485_0]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hc04, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1446, hc24, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [h1451, hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hc34, hlam, hphi, p1485_1, u4elo4]
                                            · have p1485_0 := h1485c.1
                                              have p1485_1 := h1485c.2.1
                                              have p1485_2 := h1485c.2.2.1
                                              have p1485_3 := h1485c.2.2.2
                                              linarith only [hlam, p1485_0]
                                      · linarith only [h1480, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  rcases p1457_3 (m.d 0 2) (by simp) with h1512 | h1512
                                  · linarith only [h1421, h1512, hlam]
                                  · linarith only [h0, h1512, hlam]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, h1, h1444, h1446, hlam, p1457_2]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  rcases p1457_3 (m.d 0 2) (by simp) with h1517 | h1517
                                  · linarith only [h1421, h1517, hlam]
                                  · linarith only [h1424, h1517, hlam]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1423, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1446, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1451, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1453, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1424, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1424, h1446, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h1452, hlam, p1457_0]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [h0, h1, h1424, h1444, h1451, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1457_1]
                                · have p1457_0 := h1457c.1
                                  have p1457_1 := h1457c.2.1
                                  have p1457_2 := h1457c.2.2.1
                                  have p1457_3 := h1457c.2.2.2
                                  linarith only [hlam, p1457_0]
                          · linarith only [h0, h1, h1444, h1452, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h1444, h1446, h1451, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1446, h1448, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h1446, h1447, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h1423, h1444, h1446, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h1425, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1536 | h1536
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1537 | h1537
            · linarith only [h1423, h1424, h1537, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1539 | h1539
              · linarith only [h0, h1421, h1423, h1539, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1542 | h1542
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1543 | h1543
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1544 | h1544
                      · linarith only [h1537, h1544, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1546 | h1546
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1547 | h1547
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1548 | h1548
                            · linarith only [h0, h1424, h1537, h1541, h1548, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1424, h1541, h1546, h1548, hc34, hlam, hphi, u4elo4]
                          · linarith only [h1, h1539, h1543, h1544, h1547, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h1, h1539, h1541, h1546, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h1541, h1543, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h1541, h1542, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1423, h1424, h1541, hc12, hc25, hlam, hphi]
          · linarith only [h0, h1, h1536, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1557 | h1557
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1558 | h1558
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1559 | h1559
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
              · linarith only [h0, h1423, h1560, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1562 | h1562
                · linarith only [h0, h1423, h1562, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1564 | h1564
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1565 | h1565
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1566 | h1566
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1567 | h1567
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1568 | h1568
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1569 | h1569
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1570 | h1570
                              · rcases h2bigk with h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c | h1571c
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1423, hc12, hlam, hphi, ht23, ht34, p1571_1, u4elo2]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1421, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1423, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1423, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1571_1, u4elo2]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h0, hlam, p1571_1]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1560, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1562, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h0, h1, h1560, h1568, h1570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1571_1]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  rcases p1571_3 (m.d 0 2) (by simp) with h1582 | h1582
                                  · linarith only [h1582, hlam, p1571_0]
                                  · rcases p1571_3 (m.d 1 2) (by simp) with h1584 | h1584
                                    · linarith only [h1560, h1584, hlam]
                                    · rcases p1571_3 (m.d 2 3) (by simp) with h1586 | h1586
                                      · rcases p1571_3 (m.d 2 4) (by simp) with h1587 | h1587
                                        · linarith only [h1567, h1587, hlam]
                                        · linarith only [h1423, h1587, hlam]
                                      · linarith only [h1586, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  rcases p1571_3 (m.d 0 2) (by simp) with h1591 | h1591
                                  · linarith only [h1421, h1591, hlam]
                                  · linarith only [h0, h1591, hlam]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1423, hc02, hc23, hlam, hphi, p1571_1]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  rcases p1571_3 (m.d 0 2) (by simp) with h1596 | h1596
                                  · linarith only [h1421, h1596, hlam]
                                  · linarith only [h1557, h1596, hlam]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hc02, hlam, hphi, ht23, ht34, p1571_1, u4elo2]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, p1571_1, u4elo2]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1567, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  rcases p1571_3 (m.d 0 2) (by simp) with h1603 | h1603
                                  · linarith only [h1423, h1603, hlam]
                                  · linarith only [h1557, h1603, hlam]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1557, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1423, h1557, hc12, hlam, hphi, ht23, ht34, p1571_1, u4elo0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1568, hlam, p1571_0]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [h1569, hlam, p1571_1]
                                · have p1571_0 := h1571c.1
                                  have p1571_1 := h1571c.2.1
                                  have p1571_2 := h1571c.2.2.1
                                  have p1571_3 := h1571c.2.2.2
                                  linarith only [hlam, p1571_0]
                              · linarith only [h1423, h1559, h1570, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1, h1420, h1423, h1557, h1560, h1566, h1568, h1569, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h1, h1420, h1560, h1566, h1568, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h1420, h1560, h1566, h1567, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1423, h1559, h1564, h1566, hc34, hlam, hphi, u4elo2]
                    · linarith only [h0, h1, h1565, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1420, h1562, h1564, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1423, h1557, h1559, hlam]
          · linarith only [h1, h1420, h1558, hc14, hlam, hphi, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1620 | h1620
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1621 | h1621
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1622 | h1622
              · linarith only [h0, h1, h1421, h1622, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1624 | h1624
                · linarith only [h0, h1423, h1624, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1626 | h1626
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1627 | h1627
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1628 | h1628
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1629 | h1629
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1630 | h1630
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1631 | h1631
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1632 | h1632
                              · rcases h2bigk with h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c | h1633c
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1557, h1631, hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1421, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1423, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1557, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, hlam, p1633_1]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1622, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1624, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, h1, h1557, h1622, hc02, hc23, hlam, hphi, p1633_1]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  rcases p1633_3 (m.d 0 2) (by simp) with h1644 | h1644
                                  · linarith only [h1644, hlam, p1633_0]
                                  · rcases p1633_3 (m.d 1 2) (by simp) with h1646 | h1646
                                    · linarith only [h1622, h1646, hlam]
                                    · rcases p1633_3 (m.d 2 3) (by simp) with h1648 | h1648
                                      · rcases p1633_3 (m.d 2 4) (by simp) with h1649 | h1649
                                        · linarith only [h1629, h1649, hlam]
                                        · linarith only [h1423, h1649, hlam]
                                      · linarith only [h1648, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  rcases p1633_3 (m.d 0 2) (by simp) with h1653 | h1653
                                  · linarith only [h1421, h1653, hlam]
                                  · linarith only [h0, h1653, hlam]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, h1423, hc12, hc23, hlam, hphi, p1633_1]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, h1557, hc12, hc23, hlam, hphi, p1633_1]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1629, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, h1557, hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h0, h1631, hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1631, hc12, hlam, hphi, ht23, ht34, p1633_1, u4elo2]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1630, hlam, p1633_0]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [h1631, hlam, p1633_1]
                                · have p1633_0 := h1633c.1
                                  have p1633_1 := h1633c.2.1
                                  have p1633_2 := h1633c.2.2.1
                                  have p1633_3 := h1633c.2.2.2
                                  linarith only [hlam, p1633_0]
                              · linarith only [h1423, h1621, h1632, hc34, hlam, hphi, u4elo2]
                            · linarith only [h1, h1420, h1423, h1622, h1628, h1631, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h1622, h1630, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1420, h1622, h1628, h1629, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1621, h1628, hc14, hlam, hphi, u4elo0]
                    · linarith only [h1, h1420, h1624, h1627, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1420, h1624, h1626, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1676 | h1676
              · linarith only [h0, h1423, h1676, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
                · linarith only [h0, h1423, h1621, h1678, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1681 | h1681
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1682 | h1682
                      · linarith only [h1420, h1621, h1682, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1684 | h1684
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1685 | h1685
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1686 | h1686
                            · linarith only [h1423, h1621, h1686, hc02, hlam, hphi, ht23, ht34, u4elo2]
                            · linarith only [h0, h1423, h1686, hc12, hlam, hphi, ht23, ht34, u4elo4]
                          · linarith only [h0, h1, h1676, h1685, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1, h1420, h1676, h1680, h1684, hlam]
                    · linarith only [h1, h1420, h1678, h1681, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1420, h1678, h1680, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h1420, h1620, hc14, hlam, hphi, u4elo3]
  · linarith only [h0, h1420, hc12, hlam, hphi, ht23, ht34, u4elo1]

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_12_24_L_I_M_LI_x0_x0 m hb2 hb4 h0 h1
  · exact r1l7_12_24_L_I_M_LI_x0_x1 m hb2 hb4 h0 h1

set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1695 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1696 | h1696
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1697 | h1697
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1698 | h1698
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1699 | h1699
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1700 | h1700
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1701 | h1701
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1702 | h1702
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1703 | h1703
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1704 | h1704
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1705 | h1705
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1706 | h1706
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1707 | h1707
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1708 | h1708
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1709 | h1709
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1710 | h1710
                              · linarith only [h0, h1695, h1702, h1707, h1710, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h1701, h1710, hc34, hlam, hphi, u4elo0]
                            · linarith only [h1701, h1709, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h1695, h1705, h1708, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1695, h1704, h1707, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1701, h1706, hc14, hlam, hphi, u4elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1717 | h1717
                      · linarith only [h1704, h1705, h1717, hlam]
                      · linarith only [h1701, h1717, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1720 | h1720
                    · linarith only [h0, h1695, h1700, h1704, h1720, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1722 | h1722
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1723 | h1723
                        · linarith only [h1702, h1704, h1723, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                          · linarith only [h1720, h1723, h1725, hc13, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1727 | h1727
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1728 | h1728
                              · rcases h2bigk with h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c | h1729c
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  rcases p1729_3 (m.d 0 2) (by simp) with h1732 | h1732
                                  · rcases p1729_3 (m.d 1 2) (by simp) with h1733 | h1733
                                    · rcases p1729_3 (m.d 2 3) (by simp) with h1734 | h1734
                                      · linarith only [h1734, hlam, p1729_0]
                                      · rcases p1729_3 (m.d 2 4) (by simp) with h1736 | h1736
                                        · linarith only [h1698, h1736, hlam]
                                        · linarith only [h1723, h1736, hlam]
                                    · linarith only [h1702, h1733, hlam]
                                  · linarith only [h1732, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  rcases p1729_3 (m.d 0 2) (by simp) with h1741 | h1741
                                  · rcases p1729_3 (m.d 1 2) (by simp) with h1742 | h1742
                                    · rcases p1729_3 (m.d 2 3) (by simp) with h1743 | h1743
                                      · linarith only [h1697, h1743, hlam]
                                      · rcases p1729_3 (m.d 2 4) (by simp) with h1745 | h1745
                                        · linarith only [h1745, hlam, p1729_0]
                                        · rcases p1729_3 (m.d 2 5) (by simp) with h1747 | h1747
                                          · linarith only [h1699, h1747, hlam]
                                          · rcases h4bigk with h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c | h1749c
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hc14, hlam, hphi, p1749_1, u4elo0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, h1702, h1720, h1727, h1728, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1749_1, u4elo0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1702, h1720, h1728, hc23, hlam, hphi, ht34, p1749_1, u4elo0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              rcases p1749_3 (m.d 0 4) (by simp) with h1754 | h1754
                                              · rcases p1749_3 (m.d 1 4) (by simp) with h1755 | h1755
                                                · linarith only [h1696, h1755, hlam]
                                                · linarith only [h1722, h1755, hlam]
                                              · linarith only [h1754, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1696, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, h1702, h1720, h1727, h1728, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht34, ht5b, p1749_1, u4elo1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1704, hlam, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, h1704, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1698, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1703, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1723, hlam, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p1729_1, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1700, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h0, h1695, h1700, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1749_1]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1701, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1722, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1727, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [h1728, hlam, p1749_0]
                                            · have p1749_0 := h1749c.1
                                              have p1749_1 := h1749c.2.1
                                              have p1749_2 := h1749c.2.2.1
                                              have p1749_3 := h1749c.2.2.2
                                              linarith only [hlam, p1749_0]
                                    · linarith only [h1703, h1742, hlam]
                                  · linarith only [h1741, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  rcases p1729_3 (m.d 0 2) (by simp) with h1781 | h1781
                                  · rcases p1729_3 (m.d 1 2) (by simp) with h1782 | h1782
                                    · rcases p1729_3 (m.d 2 3) (by simp) with h1783 | h1783
                                      · linarith only [h1697, h1783, hlam]
                                      · rcases p1729_3 (m.d 2 4) (by simp) with h1785 | h1785
                                        · linarith only [h1698, h1785, hlam]
                                        · linarith only [h1727, h1785, hlam]
                                    · linarith only [h0, h1782, hlam, p1729_1]
                                  · linarith only [h1781, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, h1695, h1700, h1720, h1728, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, h1695, h1700, h1702, h1720, h1728, hlam, p1729_2]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  rcases p1729_3 (m.d 0 2) (by simp) with h1793 | h1793
                                  · linarith only [h0, h1793, hlam]
                                  · linarith only [h1698, h1793, hlam]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  rcases p1729_3 (m.d 0 2) (by simp) with h1796 | h1796
                                  · linarith only [h0, h1796, hlam]
                                  · linarith only [h1699, h1796, hlam]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1697, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1702, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1723, hlam, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1725, hlam, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1698, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1703, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, p1729_1, u4elo2]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, h1695, h1700, h1703, h1704, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1699, hlam, p1729_0]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, h1695, h1700, h1702, h1720, h1728, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h0, h1695, h1700, h1725, h1728, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [h1727, hlam, p1729_1]
                                · have p1729_0 := h1729c.1
                                  have p1729_1 := h1729c.2.1
                                  have p1729_2 := h1729c.2.2.1
                                  have p1729_3 := h1729c.2.2.2
                                  linarith only [hlam, p1729_0]
                              · linarith only [h1701, h1704, h1728, hc14, hlam, hphi, u4elo0]
                            · linarith only [h0, h1695, h1700, h1704, h1722, h1727, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h1701, h1722, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h1703, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1697, h1702, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1819 | h1819
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1820 | h1820
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1821 | h1821
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1822 | h1822
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1823 | h1823
                      · linarith only [h1701, h1823, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1825 | h1825
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1826 | h1826
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1827 | h1827
                            · linarith only [h1696, h1701, h1820, h1827, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1829 | h1829
                              · linarith only [h1696, h1701, h1820, h1829, hc24, hlam, hphi, u4elo3]
                              · rcases h2bigk with h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c | h1831c
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1834 | h1834
                                  · rcases p1831_3 (m.d 1 2) (by simp) with h1835 | h1835
                                    · rcases p1831_3 (m.d 2 3) (by simp) with h1836 | h1836
                                      · linarith only [h1836, hlam, p1831_0]
                                      · rcases p1831_3 (m.d 2 4) (by simp) with h1838 | h1838
                                        · linarith only [h1698, h1838, hlam]
                                        · rcases p1831_3 (m.d 2 5) (by simp) with h1840 | h1840
                                          · linarith only [h1699, h1840, hlam]
                                          · rcases h4bigk with h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c | h1842c
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1701, h1820, h1825, hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1701, h1825, hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1701, hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1701, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1696, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1825, hc34, hlam, hphi, p1842_1, u4elo1]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1696, h1701, hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1823, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1698, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1820, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hc34, hlam, hphi, p1842_1, u4elo2]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1827, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1700, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1821, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1825, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1829, hlam, p1842_0]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hc04, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hc14, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [h1825, hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hc34, hlam, hphi, p1842_1, u4elo4]
                                            · have p1842_0 := h1842c.1
                                              have p1842_1 := h1842c.2.1
                                              have p1842_2 := h1842c.2.2.1
                                              have p1842_3 := h1842c.2.2.2
                                              linarith only [hlam, p1842_0]
                                    · linarith only [h1819, h1835, hlam]
                                  · linarith only [h1834, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1870 | h1870
                                  · rcases p1831_3 (m.d 1 2) (by simp) with h1871 | h1871
                                    · rcases p1831_3 (m.d 2 3) (by simp) with h1872 | h1872
                                      · linarith only [h1697, h1872, hlam]
                                      · linarith only [h1825, h1872, hlam]
                                    · linarith only [h1820, h1871, hlam]
                                  · linarith only [h1870, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1877 | h1877
                                  · rcases p1831_3 (m.d 1 2) (by simp) with h1878 | h1878
                                    · rcases p1831_3 (m.d 2 3) (by simp) with h1879 | h1879
                                      · linarith only [h1697, h1879, hlam]
                                      · linarith only [h1826, h1879, hlam]
                                    · linarith only [h0, h1695, h1878, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1831_1]
                                  · linarith only [h1877, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, h1695, h1821, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1831_1]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1886 | h1886
                                  · linarith only [h0, h1886, hlam]
                                  · linarith only [h1697, h1886, hlam]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1889 | h1889
                                  · linarith only [h0, h1889, hlam]
                                  · linarith only [h1698, h1889, hlam]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  rcases p1831_3 (m.d 0 2) (by simp) with h1892 | h1892
                                  · linarith only [h0, h1892, hlam]
                                  · linarith only [h1699, h1892, hlam]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1697, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1819, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, h1695, h1819, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1831_1]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, h1695, h1819, h1825, h1827, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1831_1]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1698, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1820, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1825, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1827, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1699, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1831_1]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h1826, hlam, p1831_0]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [h0, h1695, h1819, h1825, h1826, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1831_1]
                                · have p1831_0 := h1831c.1
                                  have p1831_1 := h1831c.2.1
                                  have p1831_2 := h1831c.2.2.1
                                  have p1831_3 := h1831c.2.2.2
                                  linarith only [hlam, p1831_0]
                          · linarith only [h0, h1695, h1822, h1826, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1700, h1701, h1825, hc23, hlam, hphi, ht34, u4elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1912 | h1912
                      · linarith only [h1701, h1912, hc04, hlam, hphi, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1915 | h1915
                          · linarith only [h1819, h1822, h1915, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1917 | h1917
                            · linarith only [h1696, h1701, h1820, h1917, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1919 | h1919
                              · linarith only [h1696, h1701, h1820, h1914, h1919, hlam]
                              · linarith only [h1819, h1822, h1914, h1919, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1700, h1701, h1914, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h1700, h1701, h1819, h1821, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h1820, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1697, h1819, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1926 | h1926
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1927 | h1927
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1928 | h1928
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1929 | h1929
                  · linarith only [h0, h1695, h1700, h1929, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1931 | h1931
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1932 | h1932
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1933 | h1933
                        · linarith only [h1695, h1700, h1927, h1933, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1935 | h1935
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1936 | h1936
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1937 | h1937
                              · rcases h2bigk with h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c | h1938c
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h0, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h1941 | h1941
                                  · rcases p1938_3 (m.d 1 2) (by simp) with h1942 | h1942
                                    · rcases p1938_3 (m.d 2 3) (by simp) with h1943 | h1943
                                      · linarith only [h1943, hlam, p1938_0]
                                      · rcases p1938_3 (m.d 2 4) (by simp) with h1945 | h1945
                                        · linarith only [h1698, h1945, hlam]
                                        · linarith only [h1933, h1945, hlam]
                                    · linarith only [h1927, h1942, hlam]
                                  · linarith only [h1941, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h1950 | h1950
                                  · rcases p1938_3 (m.d 1 2) (by simp) with h1951 | h1951
                                    · rcases p1938_3 (m.d 2 3) (by simp) with h1952 | h1952
                                      · linarith only [h1697, h1952, hlam]
                                      · rcases p1938_3 (m.d 2 4) (by simp) with h1954 | h1954
                                        · linarith only [h1954, hlam, p1938_0]
                                        · rcases p1938_3 (m.d 2 5) (by simp) with h1956 | h1956
                                          · linarith only [h1699, h1956, hlam]
                                          · rcases h4bigk with h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c | h1958c
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1928, hc24, hlam, hphi, p1958_1, u4elo0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hc24, hlam, hphi, p1958_1, u4elo0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1700, hlam, p1958_1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              rcases p1958_3 (m.d 0 4) (by simp) with h1963 | h1963
                                              · rcases p1958_3 (m.d 1 4) (by simp) with h1964 | h1964
                                                · linarith only [h1696, h1964, hlam]
                                                · linarith only [h1932, h1964, hlam]
                                              · linarith only [h1963, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1696, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1933, h1935, h1937, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1958_1, u4elo1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1929, hlam, p1958_1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h0, h1696, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1958_1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1698, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1928, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1933, hlam, p1958_1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1938_1, p1958_1]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hc04, hlam, hphi, p1958_1, u4elo3]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hc14, hlam, hphi, p1958_1, u4elo3]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hc24, hlam, hphi, p1958_1, u4elo3]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              rcases p1958_3 (m.d 0 4) (by simp) with h1982 | h1982
                                              · linarith only [h1700, h1982, hlam]
                                              · linarith only [h1926, h1982, hlam]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1926, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1932, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1936, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [h1937, hlam, p1958_0]
                                            · have p1958_0 := h1958c.1
                                              have p1958_1 := h1958c.2.1
                                              have p1958_2 := h1958c.2.2.1
                                              have p1958_3 := h1958c.2.2.2
                                              linarith only [hlam, p1958_0]
                                    · linarith only [h1928, h1951, hlam]
                                  · linarith only [h1950, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h1992 | h1992
                                  · rcases p1938_3 (m.d 1 2) (by simp) with h1993 | h1993
                                    · rcases p1938_3 (m.d 2 3) (by simp) with h1994 | h1994
                                      · linarith only [h1697, h1994, hlam]
                                      · linarith only [h1935, h1994, hlam]
                                    · linarith only [h0, h1695, h1927, h1935, h1993, hlam]
                                  · linarith only [h1992, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h0, h1695, h1927, h1935, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1938_1]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h2001 | h2001
                                  · linarith only [h0, h2001, hlam]
                                  · linarith only [h1697, h2001, hlam]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h2004 | h2004
                                  · linarith only [h0, h2004, hlam]
                                  · linarith only [h1698, h2004, hlam]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  rcases p1938_3 (m.d 0 2) (by simp) with h2007 | h2007
                                  · linarith only [h0, h2007, hlam]
                                  · linarith only [h1699, h2007, hlam]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1697, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1927, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1933, hlam, p1938_1]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1695, h1700, h1927, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1938_1, u4elo3]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1698, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1928, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hc23, hlam, hphi, ht34, p1938_1, u4elo2]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h0, h1696, h1928, h1935, h1937, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1938_1]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1699, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p1938_1]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1935, hlam, p1938_0]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [h1936, hlam, p1938_1]
                                · have p1938_0 := h1938c.1
                                  have p1938_1 := h1938c.2.1
                                  have p1938_2 := h1938c.2.2.1
                                  have p1938_3 := h1938c.2.2.2
                                  linarith only [hlam, p1938_0]
                              · linarith only [h1695, h1700, h1927, h1935, h1937, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h0, h1696, h1932, h1936, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1695, h1700, h1931, h1935, hc23, hlam, hphi, ht34, u4elo3]
                      · linarith only [h1700, h1926, h1932, hc14, hlam, hphi, u4elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2029 | h2029
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2030 | h2030
                        · linarith only [h1697, h1700, h2030, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2032 | h2032
                          · linarith only [h1931, h2030, h2032, hc13, hlam, hphi, ht34, u4elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2034 | h2034
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2035 | h2035
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
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2039 | h2039
                                  · rcases p2036_3 (m.d 1 2) (by simp) with h2040 | h2040
                                    · rcases p2036_3 (m.d 2 3) (by simp) with h2041 | h2041
                                      · linarith only [h2041, hlam, p2036_0]
                                      · rcases p2036_3 (m.d 2 4) (by simp) with h2043 | h2043
                                        · linarith only [h1698, h2043, hlam]
                                        · linarith only [h2030, h2043, hlam]
                                    · linarith only [h1927, h2040, hlam]
                                  · linarith only [h2039, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2048 | h2048
                                  · rcases p2036_3 (m.d 1 2) (by simp) with h2049 | h2049
                                    · rcases p2036_3 (m.d 2 3) (by simp) with h2050 | h2050
                                      · linarith only [h1697, h2050, hlam]
                                      · rcases p2036_3 (m.d 2 4) (by simp) with h2052 | h2052
                                        · linarith only [h2052, hlam, p2036_0]
                                        · rcases p2036_3 (m.d 2 5) (by simp) with h2054 | h2054
                                          · linarith only [h1699, h2054, hlam]
                                          · rcases h4bigk with h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c | h2056c
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1928, h2034, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2056_1, u4elo0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1700, h2034, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2056_1, u4elo3]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1700, hlam, p2056_1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              rcases p2056_3 (m.d 0 4) (by simp) with h2061 | h2061
                                              · rcases p2056_3 (m.d 1 4) (by simp) with h2062 | h2062
                                                · linarith only [h1696, h2062, hlam]
                                                · linarith only [h2029, h2062, hlam]
                                              · linarith only [h2061, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1696, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h2034, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p2056_1, u4elo1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1929, hlam, p2056_1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h0, h1696, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2056_1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1698, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1928, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h2030, hlam, p2056_1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hc02, hc45, hlam, hphi, ht0b, ht5b, p2036_1, p2056_1]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hc04, hlam, hphi, p2056_1, u4elo3]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1928, hc24, hlam, hphi, p2056_1, u4elo3]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hc24, hlam, hphi, p2056_1, u4elo3]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              rcases p2056_3 (m.d 0 4) (by simp) with h2080 | h2080
                                              · linarith only [h1700, h2080, hlam]
                                              · linarith only [h1926, h2080, hlam]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h1926, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h2029, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h2034, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [h2035, hlam, p2056_0]
                                            · have p2056_0 := h2056c.1
                                              have p2056_1 := h2056c.2.1
                                              have p2056_2 := h2056c.2.2.1
                                              have p2056_3 := h2056c.2.2.2
                                              linarith only [hlam, p2056_0]
                                    · linarith only [h1928, h2049, hlam]
                                  · linarith only [h2048, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2090 | h2090
                                  · rcases p2036_3 (m.d 1 2) (by simp) with h2091 | h2091
                                    · rcases p2036_3 (m.d 2 3) (by simp) with h2092 | h2092
                                      · linarith only [h1697, h2092, hlam]
                                      · rcases p2036_3 (m.d 2 4) (by simp) with h2094 | h2094
                                        · linarith only [h1698, h2094, hlam]
                                        · linarith only [h2034, h2094, hlam]
                                    · linarith only [h0, h1695, h1696, h1927, h1928, h2034, h2091, hc23, hlam, hphi, ht34, u4elo0]
                                  · linarith only [h2090, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, h1696, h1928, h2034, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2101 | h2101
                                  · linarith only [h0, h2101, hlam]
                                  · linarith only [h1697, h2101, hlam]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2104 | h2104
                                  · linarith only [h0, h2104, hlam]
                                  · linarith only [h1698, h2104, hlam]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  rcases p2036_3 (m.d 0 2) (by simp) with h2107 | h2107
                                  · linarith only [h0, h2107, hlam]
                                  · linarith only [h1699, h2107, hlam]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1697, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1927, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2030, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2032, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1698, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1928, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1696, h1928, hc23, hlam, hphi, ht34, p2036_1, u4elo0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, h1696, h1928, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1699, hlam, p2036_0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h0, hc01, hc25, hlam, hphi, ht12, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h1699, h1926, hc23, hlam, hphi, ht34, p2036_1, u4elo0]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [h2034, hlam, p2036_1]
                                · have p2036_0 := h2036c.1
                                  have p2036_1 := h2036c.2.1
                                  have p2036_2 := h2036c.2.2.1
                                  have p2036_3 := h2036c.2.2.2
                                  linarith only [hlam, p2036_0]
                              · linarith only [h0, h1696, h1700, h1928, h2034, h2035, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1926, h2034, hc24, hlam, hphi, u4elo0]
                      · linarith only [h1700, h1926, h2029, hc14, hlam, hphi, u4elo3]
                · linarith only [h0, h1928, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1695, h1697, h1927, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2130 | h2130
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2131 | h2131
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2132 | h2132
                  · linarith only [h1695, h1700, h1926, h2132, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2134 | h2134
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2135 | h2135
                      · linarith only [h1696, h1926, h2135, hlam]
                      · linarith only [h2132, h2134, h2135, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2138 | h2138
                      · linarith only [h1700, h1926, h2138, hc03, hlam, hphi, ht34, u4elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2140 | h2140
                        · linarith only [h1697, h1700, h2140, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2142 | h2142
                          · linarith only [h2130, h2134, h2142, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2144 | h2144
                            · linarith only [h1696, h1926, h2131, h2144, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2146 | h2146
                              · linarith only [h1700, h1926, h2146, hc03, hlam, hphi, ht34, u4elo3]
                              · linarith only [h1695, h1700, h2130, h2146, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h2131, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1697, h2130, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2151 | h2151
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2152 | h2152
            · linarith only [h0, h1696, h1699, h2152, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2154 | h2154
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2155 | h2155
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2156 | h2156
                  · linarith only [h0, h1695, h1699, h2152, h2156, hc34, hlam, hphi, u4elo4]
                  · linarith only [h0, h1695, h1699, h2151, h2152, h2154, h2156, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h2155, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1695, h1697, h1699, h2154, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2161 | h2161
            · linarith only [h0, h1696, h1699, h2161, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2163 | h2163
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2164 | h2164
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2165 | h2165
                  · linarith only [h1695, h2151, h2161, h2165, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2167 | h2167
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2168 | h2168
                      · linarith only [h0, h1696, h1699, h2161, h2168, hlam]
                      · linarith only [h2165, h2167, h2168, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2171 | h2171
                      · linarith only [h0, h1696, h1699, h2161, h2171, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2173 | h2173
                        · linarith only [h2151, h2163, h2167, h2173, hc03, hc35, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2175 | h2175
                          · linarith only [h2163, h2167, h2175, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2177 | h2177
                            · linarith only [h0, h1696, h1699, h2161, h2164, h2177, hlam]
                            · linarith only [h0, h1696, h1699, h2163, h2165, h2177, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h2164, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
              · linarith only [h0, h1697, h2163, hlam]
      · linarith only [h0, h1695, h1698, hc13, hlam, hphi, ht34, u4elo2]
    · linarith only [h0, h1695, h1697, hlam]
  · linarith only [h1695, h1696, hc13, hlam, hphi, ht34, u4elo1]

end R2N4
