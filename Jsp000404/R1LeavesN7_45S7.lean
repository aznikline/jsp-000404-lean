import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6122000 in
set_option maxHeartbeats 6122000 in
theorem r1l7_20_12_14_H_L_L_I_L_I_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h683 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1188 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1449 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1450 | h1450
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1451 | h1451
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1452 | h1452
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1453 | h1453
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1457 | h1457
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1458 | h1458
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1459 | h1459
                    · linarith only [h1449, h1459, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1449, h1452, h1459, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1188, h1453, h1458, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                · linarith only [h1452, h1457, h683, hlam]
              · linarith only [h0, h1451, h1456, hlam]
            · linarith only [h0, h1450, h1455, hlam]
          · linarith only [h0, h1449, h1454, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1467 | h1467
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1468 | h1468
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1469 | h1469
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1470 | h1470
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1471 | h1471
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1472 | h1472
                    · linarith only [h1449, h1472, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1452, h1472, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1475 | h1475
                    · linarith only [h1449, h1475, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1449, h1452, h1475, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1449, h1452, h1470, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1451, h1469, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1450, h1468, hlam]
          · linarith only [h0, h1449, h1467, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1482 | h1482
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1483 | h1483
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1484 | h1484
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1486 | h1486
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1487 | h1487
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1488 | h1488
                    · linarith only [h1449, h1452, h1488, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1490 | h1490
                      · linarith only [h1449, h1490, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1492 | h1492
                        · linarith only [h1450, h1492, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1450, h1482, h1488, h1492, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1482, h1487, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1496 | h1496
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1497 | h1497
                    · linarith only [h1486, h1497, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1499 | h1499
                      · linarith only [h1450, h1497, h1499, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1501 | h1501
                        · linarith only [h1450, h1501, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · linarith only [h1450, h1482, h1497, h1501, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1450, h1482, h1486, h1496, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1451, h1485, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1450, h1484, hlam]
          · linarith only [h0, h1449, h1483, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1510 | h1510
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1511 | h1511
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1512 | h1512
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1513 | h1513
                    · linarith only [h1449, h1452, h1513, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1515 | h1515
                      · linarith only [h1449, h1515, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1517 | h1517
                        · linarith only [h1450, h1482, h1517, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1519 | h1519
                          · linarith only [h1452, h1482, h1508, h1511, h1519, h683, hc01, hc12, hlam, hphi]
                          · linarith only [h1452, h1512, h1519, h683, hc01, hc14, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1522 | h1522
                    · linarith only [h1449, h1452, h1522, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1524 | h1524
                      · linarith only [h1449, h1524, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1526 | h1526
                        · linarith only [h1450, h1512, h1526, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1528 | h1528
                          · linarith only [h1511, h1512, h1528, hlam]
                          · rcases h2bigk with h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c | h1530c
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h0, hlam, p1530_1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1526, hc24, hlam, hphi, ht0b, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              rcases p1530_3 (m.d 0 2) (by simp) with h1536 | h1536
                              · linarith only [h0, h1536, hlam]
                              · rcases p1530_3 (m.d 1 2) (by simp) with h1538 | h1538
                                · rcases p1530_3 (m.d 2 3) (by simp) with h1539 | h1539
                                  · linarith only [h1508, h1539, hlam]
                                  · rcases p1530_3 (m.d 2 4) (by simp) with h1541 | h1541
                                    · linarith only [h1509, h1541, hlam]
                                    · rcases p1530_3 (m.d 2 5) (by simp) with h1543 | h1543
                                      · linarith only [h1510, h1543, hlam]
                                      · rcases h4bigk with h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c | h1545c
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1188, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1522, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1545_1, u0elo3]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1452, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1482, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1512, hc04, hc45, hlam, hphi, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1512, h1522, hc23, hc45, hlam, hphi, ht34, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1451, h1452, h1512, h1522, h1526, h683, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p1530_1, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1512, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1450, hlam, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1509, hlam, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1522, hlam, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1526, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1452, h1508, h1511, h683, hc01, hc12, hlam, hphi, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1511, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1511, h1512, h1522, hc23, hc45, hlam, hphi, ht34, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1528, hlam, p1545_0]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          rcases p1545_3 (m.d 0 4) (by simp) with h1566 | h1566
                                          · linarith only [h1566, hlam, p1545_0]
                                          · rcases p1545_3 (m.d 1 4) (by simp) with h1568 | h1568
                                            · linarith only [h1512, h1568, hlam]
                                            · linarith only [h1188, h1568, hlam]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1188, h1451, h1522, h1526, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p1530_1, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          rcases p1545_3 (m.d 0 4) (by simp) with h1572 | h1572
                                          · linarith only [h1482, h1572, hlam]
                                          · linarith only [h1450, h1572, hlam]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [h1451, h1452, h1522, h1526, h683, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p1530_1, p1545_1]
                                        · have p1545_0 := h1545c.1
                                          have p1545_1 := h1545c.2.1
                                          have p1545_2 := h1545c.2.2.1
                                          have p1545_3 := h1545c.2.2.2
                                          linarith only [hlam, p1545_0]
                                · linarith only [h0, h1538, hlam]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              rcases p1530_3 (m.d 0 2) (by simp) with h1579 | h1579
                              · linarith only [h0, h1579, hlam]
                              · linarith only [h1449, h1579, hlam]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              rcases p1530_3 (m.d 0 2) (by simp) with h1582 | h1582
                              · linarith only [h0, h1582, hlam]
                              · linarith only [h1450, h1582, hlam]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              rcases p1530_3 (m.d 0 2) (by simp) with h1585 | h1585
                              · linarith only [h0, h1585, hlam]
                              · linarith only [h1451, h1585, hlam]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1449, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1508, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1522, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1524, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1450, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1509, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1451, h1526, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1526, hlam, p1530_1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1451, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1510, hlam, p1530_0]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1451, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [h1451, hc24, hlam, hphi, ht0b, ht45, ht5b, p1530_1, u0elo1]
                            · have p1530_0 := h1530c.1
                              have p1530_1 := h1530c.2.1
                              have p1530_2 := h1530c.2.2.1
                              have p1530_3 := h1530c.2.2.2
                              linarith only [hlam, p1530_0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1603 | h1603
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1604 | h1604
                    · linarith only [h1511, h1604, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1606 | h1606
                      · linarith only [h1449, h1606, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1608 | h1608
                        · linarith only [h1450, h1452, h1482, h1608, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1610 | h1610
                          · rcases h2bigk with h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c | h1611c
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h0, hlam, p1611_1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hc25, hlam, hphi, ht0b, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              rcases p1611_3 (m.d 0 2) (by simp) with h1617 | h1617
                              · linarith only [h0, h1617, hlam]
                              · rcases p1611_3 (m.d 1 2) (by simp) with h1619 | h1619
                                · rcases p1611_3 (m.d 2 3) (by simp) with h1620 | h1620
                                  · linarith only [h1508, h1620, hlam]
                                  · rcases p1611_3 (m.d 2 4) (by simp) with h1622 | h1622
                                    · linarith only [h1509, h1622, hlam]
                                    · rcases p1611_3 (m.d 2 5) (by simp) with h1624 | h1624
                                      · linarith only [h1510, h1624, hlam]
                                      · rcases h4bigk with h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c | h1626c
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1188, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1604, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1626_1, u0elo3]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1452, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1482, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          rcases p1626_3 (m.d 0 4) (by simp) with h1632 | h1632
                                          · linarith only [h1188, h1632, hlam]
                                          · rcases p1626_3 (m.d 1 4) (by simp) with h1634 | h1634
                                            · rcases p1626_3 (m.d 2 4) (by simp) with h1635 | h1635
                                              · linarith only [h1509, h1635, hlam]
                                              · rcases p1626_3 (m.d 3 4) (by simp) with h1637 | h1637
                                                · rcases p1626_3 (m.d 4 5) (by simp) with h1638 | h1638
                                                  · linarith only [h1603, h1638, hlam]
                                                  · linarith only [h1482, h1638, hlam]
                                                · linarith only [h1452, h1637, hlam]
                                            · linarith only [h1188, h1634, hlam]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          rcases p1626_3 (m.d 0 4) (by simp) with h1644 | h1644
                                          · linarith only [h1188, h1644, hlam]
                                          · linarith only [h1450, h1644, hlam]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1511, hlam, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1188, h1482, h1511, hc01, hc34, hlam, hphi, ht12, ht23, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1450, hlam, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1509, hlam, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1604, hlam, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1608, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          rcases p1626_3 (m.d 0 4) (by simp) with h1654 | h1654
                                          · linarith only [h1452, h1654, hlam]
                                          · rcases p1626_3 (m.d 1 4) (by simp) with h1656 | h1656
                                            · linarith only [h1511, h1656, hlam]
                                            · linarith only [h1188, h1656, hlam]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1188, h1451, h1604, h1608, hc01, hc12, hc23, hc34, hlam, hphi, p1611_1, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          rcases p1626_3 (m.d 0 4) (by simp) with h1660 | h1660
                                          · linarith only [h1452, h1660, hlam]
                                          · linarith only [h1450, h1660, hlam]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1451, h1452, h1482, h1604, h1608, h683, hc01, hc12, hc23, hc34, hlam, hphi, p1611_1, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1452, h1603, h683, hc01, hc14, hlam, hphi, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1603, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1511, h1603, h1604, hc23, hc34, hlam, hphi, p1626_1]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [h1610, hlam, p1626_0]
                                        · have p1626_0 := h1626c.1
                                          have p1626_1 := h1626c.2.1
                                          have p1626_2 := h1626c.2.2.1
                                          have p1626_3 := h1626c.2.2.2
                                          linarith only [hlam, p1626_0]
                                · linarith only [h0, h1619, hlam]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              rcases p1611_3 (m.d 0 2) (by simp) with h1672 | h1672
                              · linarith only [h0, h1672, hlam]
                              · linarith only [h1449, h1672, hlam]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              rcases p1611_3 (m.d 0 2) (by simp) with h1675 | h1675
                              · linarith only [h0, h1675, hlam]
                              · linarith only [h1450, h1675, hlam]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              rcases p1611_3 (m.d 0 2) (by simp) with h1678 | h1678
                              · linarith only [h0, h1678, hlam]
                              · linarith only [h1451, h1678, hlam]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1449, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1508, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1604, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1606, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1450, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1509, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1451, h1608, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1608, hlam, p1611_1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1451, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1510, hlam, p1611_0]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1451, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [h1451, hc24, hlam, hphi, ht0b, ht45, ht5b, p1611_1, u0elo1]
                            · have p1611_0 := h1611c.1
                              have p1611_1 := h1611c.2.1
                              have p1611_2 := h1611c.2.2.1
                              have p1611_3 := h1611c.2.2.2
                              linarith only [hlam, p1611_0]
                          · linarith only [h1511, h1603, h1610, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1697 | h1697
                    · linarith only [h1449, h1697, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1699 | h1699
                      · linarith only [h1449, h1699, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1701 | h1701
                        · linarith only [h1450, h1603, h1701, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1703 | h1703
                          · linarith only [h1188, h1603, h1703, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1511, h1703, h683, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h1451, h1510, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1450, h1509, hlam]
          · linarith only [h0, h1449, h1450, h1508, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1709 | h1709
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1710 | h1710
        · linarith only [h1449, h1451, h1709, h1710, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1712 | h1712
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1713 | h1713
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1714 | h1714
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1715 | h1715
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1716 | h1716
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1717 | h1717
                    · linarith only [h1449, h1717, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1449, h1451, h1709, h1717, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1720 | h1720
                    · linarith only [h1449, h1451, h1720, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h1449, h1451, h1709, h1720, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h1449, h1451, h1709, h1715, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1724 | h1724
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1725 | h1725
                  · linarith only [h1188, h1710, h1712, h1714, h1724, h1725, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1727 | h1727
                    · linarith only [h1449, h1727, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · linarith only [h1449, h1451, h1709, h1727, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h1709, h1724, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
            · linarith only [h1450, h1451, h1713, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h1449, h1712, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1733 | h1733
        · linarith only [h1450, h1451, h1733, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1735 | h1735
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1736 | h1736
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1737 | h1737
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1738 | h1738
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1739 | h1739
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1740 | h1740
                    · linarith only [h1449, h1709, h1740, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1742 | h1742
                      · linarith only [h1450, h1451, h1740, h1742, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1744 | h1744
                        · linarith only [h1450, h1451, h1733, h1744, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1746 | h1746
                          · linarith only [h1450, h1451, h1740, h1744, h1746, hc23, hc34, hlam, hphi]
                          · linarith only [h1709, h1735, h1738, h1739, h1746, h683, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1749 | h1749
                    · linarith only [h1449, h1709, h1749, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1751 | h1751
                      · linarith only [h1450, h1451, h1737, h1749, h1751, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1753 | h1753
                        · linarith only [h1450, h1451, h1737, h1739, h1753, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1755 | h1755
                          · linarith only [h1738, h1739, h1755, hlam]
                          · rcases h2bigk with h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c | h1757c
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h0, hlam, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1451, h1737, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1451, h1737, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1451, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              rcases p1757_3 (m.d 0 2) (by simp) with h1763 | h1763
                              · linarith only [h0, h1763, hlam]
                              · rcases p1757_3 (m.d 1 2) (by simp) with h1765 | h1765
                                · rcases p1757_3 (m.d 2 3) (by simp) with h1766 | h1766
                                  · linarith only [h1735, h1766, hlam]
                                  · rcases p1757_3 (m.d 2 4) (by simp) with h1768 | h1768
                                    · linarith only [h1736, h1768, hlam]
                                    · rcases p1757_3 (m.d 2 5) (by simp) with h1770 | h1770
                                      · linarith only [h1737, h1770, hlam]
                                      · linarith only [h1451, h1770, hlam]
                                · linarith only [h0, h1765, hlam]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1449, h1451, h1737, hlam, p1757_2]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1450, h1451, h1737, hlam, p1757_2]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1450, h1451, h1749, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1449, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1735, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1749, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1751, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1450, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1736, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1450, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1757_1, u0elo1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1753, hlam, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1449, h1751, hc23, hc35, hlam, hphi, p1757_1]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [h1737, hlam, p1757_0]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              rcases p1757_3 (m.d 0 2) (by simp) with h1790 | h1790
                              · linarith only [h1451, h1790, hlam]
                              · linarith only [h1449, h1790, hlam]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              rcases p1757_3 (m.d 0 2) (by simp) with h1793 | h1793
                              · linarith only [h1451, h1793, hlam]
                              · linarith only [h1450, h1793, hlam]
                            · have p1757_0 := h1757c.1
                              have p1757_1 := h1757c.2.1
                              have p1757_2 := h1757c.2.2.1
                              have p1757_3 := h1757c.2.2.2
                              linarith only [hlam, p1757_0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1797 | h1797
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1798 | h1798
                    · linarith only [h1738, h1798, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1800 | h1800
                      · linarith only [h1450, h1798, h1800, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1802 | h1802
                        · linarith only [h1450, h1451, h1709, h1733, h1737, h1802, h683, hc01, hc12, hlam, hphi]
                        · linarith only [h1450, h1451, h1738, h1797, h1798, h1802, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1805 | h1805
                    · linarith only [h1449, h1805, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1807 | h1807
                      · linarith only [h1450, h1451, h1805, h1807, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1809 | h1809
                        · linarith only [h1450, h1451, h1797, h1809, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1811 | h1811
                          · linarith only [h1738, h1797, h1811, h683, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1738, h1811, h683, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1814 | h1814
                · linarith only [h1709, h1735, h1737, h1814, h683, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1816 | h1816
                  · linarith only [h1709, h1733, h1736, h1737, h1816, h683, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1818 | h1818
                    · linarith only [h1814, h1818, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1820 | h1820
                      · linarith only [h1450, h1451, h1818, h1820, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1822 | h1822
                        · linarith only [h1450, h1451, h1816, h1822, hc15, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1824 | h1824
                          · linarith only [h0, h1737, h1822, h1824, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h1814, h1824, h683, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h1450, h1451, h1736, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h0, h1449, h1451, h1735, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1829 | h1829
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1830 | h1830
      · linarith only [h1449, h1450, h1830, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1832 | h1832
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1833 | h1833
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1834 | h1834
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1835 | h1835
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1836 | h1836
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1837 | h1837
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1838 | h1838
                    · linarith only [h1449, h1450, h1830, h1834, h1838, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1840 | h1840
                      · linarith only [h1449, h1450, h1833, h1836, h1838, h1840, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1842 | h1842
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1843 | h1843
                          · rcases h2bigk with h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c | h1844c
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h0, hlam, p1844_1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1450, h1833, h1836, h1838, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1844_1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1450, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1450, h1833, h1836, h1838, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1844_1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              rcases p1844_3 (m.d 0 2) (by simp) with h1850 | h1850
                              · linarith only [h0, h1850, hlam]
                              · rcases p1844_3 (m.d 1 2) (by simp) with h1852 | h1852
                                · rcases p1844_3 (m.d 2 3) (by simp) with h1853 | h1853
                                  · linarith only [h1833, h1853, hlam]
                                  · rcases p1844_3 (m.d 2 4) (by simp) with h1855 | h1855
                                    · linarith only [h1834, h1855, hlam]
                                    · linarith only [h1450, h1855, hlam]
                                · linarith only [h0, h1852, hlam]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1449, h1450, h1833, h1836, h1838, hlam, p1844_2]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1450, h1829, h1840, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1844_1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1450, h1829, h1834, hlam, p1844_2]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1449, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1833, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1838, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1840, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1829, h1834, h1840, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1844_1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1834, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              rcases p1844_3 (m.d 0 2) (by simp) with h1870 | h1870
                              · linarith only [h1450, h1870, hlam]
                              · linarith only [h1449, h1870, hlam]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              rcases p1844_3 (m.d 0 2) (by simp) with h1874 | h1874
                              · linarith only [h1450, h1874, hlam]
                              · linarith only [h1829, h1874, hlam]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1829, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1835, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1829, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1844_1, u0elo1]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [h1842, hlam, p1844_0]
                            · have p1844_0 := h1844c.1
                              have p1844_1 := h1844c.2.1
                              have p1844_2 := h1844c.2.2.1
                              have p1844_3 := h1844c.2.2.2
                              linarith only [hlam, p1844_0]
                          · linarith only [h1449, h1450, h1838, h1843, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1450, h1829, h1832, h1840, h1842, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1449, h1450, h1832, h1834, h1837, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1885 | h1885
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1886 | h1886
                    · linarith only [h1449, h1836, h1886, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1888 | h1888
                      · linarith only [h1449, h1450, h1834, h1888, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1890 | h1890
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1891 | h1891
                          · rcases h2bigk with h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c | h1892c
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h0, hlam, p1892_1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1450, h1834, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1892_1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1450, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1450, h1834, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1892_1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              rcases p1892_3 (m.d 0 2) (by simp) with h1898 | h1898
                              · linarith only [h0, h1898, hlam]
                              · rcases p1892_3 (m.d 1 2) (by simp) with h1900 | h1900
                                · rcases p1892_3 (m.d 2 3) (by simp) with h1901 | h1901
                                  · linarith only [h1833, h1901, hlam]
                                  · rcases p1892_3 (m.d 2 4) (by simp) with h1903 | h1903
                                    · linarith only [h1834, h1903, hlam]
                                    · linarith only [h1450, h1903, hlam]
                                · linarith only [h0, h1900, hlam]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1449, h1450, h1834, hlam, p1892_2]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h0, h1450, hc01, hc12, hlam, hphi, p1892_1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1450, h1829, h1834, hlam, p1892_2]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1449, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1833, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1886, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1888, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1829, h1834, h1836, h1888, hc23, hc34, hlam, hphi, p1892_1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1834, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              rcases p1892_3 (m.d 0 2) (by simp) with h1918 | h1918
                              · linarith only [h1450, h1918, hlam]
                              · linarith only [h1449, h1918, hlam]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              rcases p1892_3 (m.d 0 2) (by simp) with h1922 | h1922
                              · linarith only [h1450, h1922, hlam]
                              · linarith only [h1829, h1922, hlam]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1829, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1835, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1829, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1892_1, u0elo1]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [h1890, hlam, p1892_0]
                            · have p1892_0 := h1892c.1
                              have p1892_1 := h1892c.2.1
                              have p1892_2 := h1892c.2.2.1
                              have p1892_3 := h1892c.2.2.2
                              linarith only [hlam, p1892_0]
                          · linarith only [h1832, h1836, h1891, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1450, h1832, h1890, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1449, h1450, h1832, h1834, h1885, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
              · linarith only [h1829, h1835, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1934 | h1934
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1935 | h1935
                · linarith only [h1830, h1833, h1834, h1935, h683, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1937 | h1937
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1938 | h1938
                    · linarith only [h1935, h1938, h683, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1940 | h1940
                      · linarith only [h1449, h1450, h1940, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1942 | h1942
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1943 | h1943
                          · rcases h2bigk with h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c | h1944c
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h0, hlam, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1450, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1944_1, u0elo3]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1450, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1450, hc25, hlam, hphi, ht0b, ht5b, p1944_1, u0elo3]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1834, h1938, hc02, hc34, hlam, hphi, ht23, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1834, h1938, hc23, hc34, hlam, hphi, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1834, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1834, h1938, h1940, hc23, hc34, hlam, hphi, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1449, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1833, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1938, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1940, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1449, h1938, hc23, hc34, hlam, hphi, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h0, h1938, hc01, hc34, hlam, hphi, ht12, ht23, p1944_1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              rcases p1944_3 (m.d 0 2) (by simp) with h1962 | h1962
                              · linarith only [h1450, h1962, hlam]
                              · linarith only [h1449, h1962, hlam]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              rcases p1944_3 (m.d 0 2) (by simp) with h1966 | h1966
                              · linarith only [h1450, h1966, hlam]
                              · linarith only [h1829, h1966, hlam]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1829, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1934, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1829, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1944_1, u0elo1]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [h1942, hlam, p1944_0]
                            · have p1944_0 := h1944c.1
                              have p1944_1 := h1944c.2.1
                              have p1944_2 := h1944c.2.2.1
                              have p1944_3 := h1944c.2.2.2
                              linarith only [hlam, p1944_0]
                          · linarith only [h1449, h1450, h1938, h1943, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h1832, h1833, h1834, h1942, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1832, h1937, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h1829, h1833, h1934, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h0, h1449, h1833, hlam]
        · linarith only [h1450, h1829, h1832, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1980 | h1980
      · linarith only [h1449, h1450, h1980, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1982 | h1982
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1983 | h1983
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1984 | h1984
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1985 | h1985
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1986 | h1986
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1987 | h1987
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1988 | h1988
                    · linarith only [h1449, h1450, h1980, h1984, h1988, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1990 | h1990
                      · linarith only [h1449, h1450, h1983, h1986, h1988, h1990, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1992 | h1992
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1993 | h1993
                          · rcases h2bigk with h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c | h1994c
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h0, hlam, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1829, h1983, h1986, h1988, h1992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1450, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1829, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              rcases p1994_3 (m.d 0 2) (by simp) with h2000 | h2000
                              · linarith only [h0, h2000, hlam]
                              · rcases p1994_3 (m.d 1 2) (by simp) with h2002 | h2002
                                · rcases p1994_3 (m.d 2 3) (by simp) with h2003 | h2003
                                  · linarith only [h1983, h2003, hlam]
                                  · rcases p1994_3 (m.d 2 4) (by simp) with h2005 | h2005
                                    · linarith only [h1984, h2005, hlam]
                                    · linarith only [h1450, h2005, hlam]
                                · linarith only [h0, h2002, hlam]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1829, h1983, h1986, h1988, h1992, hlam, p1994_2]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1829, h1992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1829, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1983, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1988, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1990, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1984, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1984, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              rcases p1994_3 (m.d 0 2) (by simp) with h2020 | h2020
                              · linarith only [h1450, h2020, hlam]
                              · linarith only [h1449, h2020, hlam]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1829, h1983, h1986, h1988, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1449, h1990, hc23, hc35, hlam, hphi, p1994_1]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1985, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              rcases p1994_3 (m.d 0 2) (by simp) with h2027 | h2027
                              · linarith only [h1829, h2027, hlam]
                              · linarith only [h1449, h2027, hlam]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [h1992, hlam, p1994_0]
                            · have p1994_0 := h1994c.1
                              have p1994_1 := h1994c.2.1
                              have p1994_2 := h1994c.2.2.1
                              have p1994_3 := h1994c.2.2.2
                              linarith only [hlam, p1994_0]
                          · linarith only [h1982, h1988, h1993, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1449, h1450, h1982, h1992, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1982, h1987, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2035 | h2035
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2036 | h2036
                    · linarith only [h1449, h1986, h2036, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2038 | h2038
                      · linarith only [h1449, h1829, h1982, h2038, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2040 | h2040
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2041 | h2041
                          · rcases h2bigk with h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c | h2042c
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h0, hlam, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1829, h1982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2042_1, u0elo3]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1450, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1829, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              rcases p2042_3 (m.d 0 2) (by simp) with h2048 | h2048
                              · linarith only [h0, h2048, hlam]
                              · rcases p2042_3 (m.d 1 2) (by simp) with h2050 | h2050
                                · rcases p2042_3 (m.d 2 3) (by simp) with h2051 | h2051
                                  · linarith only [h1983, h2051, hlam]
                                  · rcases p2042_3 (m.d 2 4) (by simp) with h2053 | h2053
                                    · linarith only [h1984, h2053, hlam]
                                    · linarith only [h1450, h2053, hlam]
                                · linarith only [h0, h2050, hlam]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, h1829, h1984, h2040, hlam, p2042_2]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h0, h1829, h2040, hc01, hc12, hlam, hphi, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, h1829, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1983, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h2036, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h2038, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, h1984, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1984, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              rcases p2042_3 (m.d 0 2) (by simp) with h2068 | h2068
                              · linarith only [h1450, h2068, hlam]
                              · linarith only [h1449, h2068, hlam]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, h1829, h1984, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1449, h2038, hc23, hc35, hlam, hphi, p2042_1]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h1985, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              rcases p2042_3 (m.d 0 2) (by simp) with h2075 | h2075
                              · linarith only [h1829, h2075, hlam]
                              · linarith only [h1449, h2075, hlam]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [h2040, hlam, p2042_0]
                            · have p2042_0 := h2042c.1
                              have p2042_1 := h2042c.2.1
                              have p2042_2 := h2042c.2.2.1
                              have p2042_3 := h2042c.2.2.2
                              linarith only [hlam, p2042_0]
                          · linarith only [h1982, h1986, h2041, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1449, h1450, h1982, h2040, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1982, h2035, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h1449, h1450, h1984, h1985, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2084 | h2084
              · linarith only [h1449, h1829, h1984, h2084, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2086 | h2086
                · linarith only [h1980, h1983, h1984, h2086, h683, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2088 | h2088
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2089 | h2089
                    · linarith only [h1449, h2086, h2089, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2091 | h2091
                      · linarith only [h1449, h1829, h1982, h2091, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2093 | h2093
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2094 | h2094
                          · rcases h2bigk with h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c | h2095c
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, hlam, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1829, h1982, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2095_1, u0elo3]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1450, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1829, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2084, h2089, h2093, hc02, hc34, hlam, hphi, ht23, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2084, h2089, h2093, hc23, hc34, hlam, hphi, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1984, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2084, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1449, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1983, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2089, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2091, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1449, h2089, hc23, hc34, hlam, hphi, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h0, h2089, hc01, hc34, hlam, hphi, ht12, ht23, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              rcases p2095_3 (m.d 0 2) (by simp) with h2113 | h2113
                              · linarith only [h1450, h2113, hlam]
                              · linarith only [h1449, h2113, hlam]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1449, h1829, h2089, hc23, hc34, hlam, hphi, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1449, h2091, hc23, hc35, hlam, hphi, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h1983, h2091, h683, hc01, hc35, hlam, hphi, ht12, ht23, p2095_1]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              rcases p2095_3 (m.d 0 2) (by simp) with h2120 | h2120
                              · linarith only [h1829, h2120, hlam]
                              · linarith only [h1449, h2120, hlam]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [h2093, hlam, p2095_0]
                            · have p2095_0 := h2095c.1
                              have p2095_1 := h2095c.2.1
                              have p2095_2 := h2095c.2.2.1
                              have p2095_3 := h2095c.2.2.2
                              linarith only [hlam, p2095_0]
                          · linarith only [h1982, h2089, h2094, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h1982, h1983, h1984, h2093, h683, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h1188, h1982, h2088, hlam]
          · linarith only [h1449, h1983, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2129 | h2129
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2130 | h2130
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2131 | h2131
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2132 | h2132
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2133 | h2133
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2134 | h2134
                    · linarith only [h1449, h1450, h1980, h1982, h2129, h2132, h2133, h2134, h683, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2136 | h2136
                      · linarith only [h1449, h1450, h1982, h2129, h2132, h2133, h2136, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2138 | h2138
                        · linarith only [h1449, h1450, h1982, h2129, h2132, h2134, h2138, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h1449, h1450, h2138, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h1449, h1450, h2130, h2133, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2142 | h2142
                  · linarith only [h1449, h1450, h1982, h2132, h2142, hc23, hc34, hlam, hphi]
                  · linarith only [h1449, h1450, h2130, h2142, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1449, h1450, h2130, h2131, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2146 | h2146
              · linarith only [h1449, h1829, h2130, h2146, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2148 | h2148
                · linarith only [h1980, h2129, h2130, h2148, h683, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2150 | h2150
                  · linarith only [h1449, h1450, h1982, h2148, h2150, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2152 | h2152
                    · linarith only [h1449, h2152, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2154 | h2154
                      · linarith only [h1449, h1450, h1982, h2154, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2156 | h2156
                        · linarith only [h0, h2130, h2150, h2152, h2156, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1449, h1450, h2156, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1449, h2129, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]

end R2N4
