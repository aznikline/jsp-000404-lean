import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_56S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1471 | h1471
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1472 | h1472
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1473 | h1473
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1474 | h1474
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1475 | h1475
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1476 | h1476
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1477 | h1477
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1478 | h1478
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1479 | h1479
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1480 | h1480
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1481 | h1481
                      · linarith only [h0, h1471, h1481, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1471, h1475, h1481, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1471, h1474, h1480, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h1471, h1473, h1478, h1479, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1478, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1487 | h1487
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1488 | h1488
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1489 | h1489
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1490 | h1490
                      · linarith only [h0, h1471, h1490, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1471, h1475, h1490, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h1471, h1474, h1489, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h1473, h1477, h1488, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                · linarith only [h0, h1471, h1487, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1475, h1476, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1497 | h1497
            · linarith only [h1475, h1497, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1499 | h1499
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1500 | h1500
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1501 | h1501
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1502 | h1502
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1503 | h1503
                      · linarith only [h1475, h1503, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1505 | h1505
                        · linarith only [h0, h1471, h1497, h1505, hc12, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1507 | h1507
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1508 | h1508
                            · linarith only [h0, h1471, h1475, h1500, h1508, hc12, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1510 | h1510
                              · linarith only [h0, h1471, h1497, h1500, h1510, hc12, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1512 | h1512
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1513 | h1513
                                  · rcases h2bigk with h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c | h1514c
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, hlam, p1514_1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1517 | h1517
                                      · rcases p1514_3 (m.d 1 2) (by simp) with h1518 | h1518
                                        · rcases p1514_3 (m.d 2 3) (by simp) with h1519 | h1519
                                          · linarith only [h1519, hlam, p1514_0]
                                          · rcases p1514_3 (m.d 2 4) (by simp) with h1521 | h1521
                                            · linarith only [h1473, h1521, hlam]
                                            · linarith only [h1508, h1521, hlam]
                                        · linarith only [h1500, h1518, hlam]
                                      · linarith only [h1517, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1526 | h1526
                                      · rcases p1514_3 (m.d 1 2) (by simp) with h1527 | h1527
                                        · rcases p1514_3 (m.d 2 3) (by simp) with h1528 | h1528
                                          · linarith only [h1472, h1528, hlam]
                                          · rcases p1514_3 (m.d 2 4) (by simp) with h1530 | h1530
                                            · linarith only [h1530, hlam, p1514_0]
                                            · rcases p1514_3 (m.d 2 5) (by simp) with h1532 | h1532
                                              · linarith only [h1474, h1532, hlam]
                                              · rcases h3bigk with h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c | h1534c
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1497, h1513, hc34, hlam, hphi, p1534_1, u3ehi1]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1497, h1513, hc34, hlam, hphi, p1534_1, u3ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1475, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1497, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1471, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h0, h1471, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1534_1, u3ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1503, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1505, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1472, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1500, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1508, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1510, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p1534_1, u3ehi0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p1534_1, u3ehi1]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p1534_1, u3ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p1534_1, u3ehi4]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p1534_1, u0ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1500, hc35, hlam, hphi, p1534_1, u3ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hc35, hlam, hphi, p1534_1, u3ehi2]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [h1513, hlam, p1534_0]
                                                · have p1534_0 := h1534c.1
                                                  have p1534_1 := h1534c.2.1
                                                  have p1534_2 := h1534c.2.2.1
                                                  have p1534_3 := h1534c.2.2.2
                                                  linarith only [hlam, p1534_0]
                                        · linarith only [h1501, h1527, hlam]
                                      · linarith only [h1526, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1562 | h1562
                                      · rcases p1514_3 (m.d 1 2) (by simp) with h1563 | h1563
                                        · rcases p1514_3 (m.d 2 3) (by simp) with h1564 | h1564
                                          · linarith only [h1472, h1564, hlam]
                                          · rcases p1514_3 (m.d 2 4) (by simp) with h1566 | h1566
                                            · linarith only [h1473, h1566, hlam]
                                            · linarith only [h1512, h1566, hlam]
                                        · linarith only [h1502, h1563, hlam]
                                      · linarith only [h1562, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1514_1, u0ehi1]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1573 | h1573
                                      · linarith only [h0, h1573, hlam]
                                      · linarith only [h1472, h1573, hlam]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1576 | h1576
                                      · linarith only [h0, h1576, hlam]
                                      · linarith only [h1473, h1576, hlam]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      rcases p1514_3 (m.d 0 2) (by simp) with h1579 | h1579
                                      · linarith only [h0, h1579, hlam]
                                      · linarith only [h1474, h1579, hlam]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1472, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1500, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1508, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1510, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1473, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1501, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1473, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi2]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, h1473, h1510, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi2]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1474, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1502, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h0, h1474, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1514_1, u3ehi2]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [h1512, hlam, p1514_0]
                                    · have p1514_0 := h1514c.1
                                      have p1514_1 := h1514c.2.1
                                      have p1514_2 := h1514c.2.2.1
                                      have p1514_3 := h1514c.2.2.2
                                      linarith only [hlam, p1514_0]
                                  · linarith only [h0, h1473, h1512, h1513, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1475, h1499, h1508, h1512, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h1475, h1499, h1500, h1503, h1507, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h0, h1471, h1500, h1502, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1471, h1500, h1501, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1471, h1500, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1604 | h1604
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1605 | h1605
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1606 | h1606
                      · linarith only [h0, h1471, h1606, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1608 | h1608
                        · linarith only [h0, h1471, h1497, h1608, hc12, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1610 | h1610
                          · linarith only [h1499, h1610, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1612 | h1612
                            · linarith only [h1472, h1497, h1612, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1614 | h1614
                              · linarith only [h0, h1471, h1603, h1614, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1616 | h1616
                                · linarith only [h1473, h1475, h1499, h1616, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1618 | h1618
                                  · linarith only [h1475, h1499, h1618, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                  · linarith only [h1475, h1618, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                    · linarith only [h0, h1471, h1474, h1605, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · linarith only [h0, h1471, h1473, h1604, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1471, h1603, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1624 | h1624
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1625 | h1625
            · linarith only [h0, h1471, h1474, h1625, hlam]
            · linarith only [h1624, h1625, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1628 | h1628
            · linarith only [h1624, h1628, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1630 | h1630
              · linarith only [h1473, h1474, h1630, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1632 | h1632
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1633 | h1633
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1634 | h1634
                    · linarith only [h0, h1474, h1634, hc12, hlam, hphi, ht01, u0ehi0]
                    · linarith only [h0, h1471, h1632, h1634, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1471, h1473, h1632, h1633, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1471, h1632, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1639 | h1639
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1640 | h1640
          · linarith only [h0, h1471, h1473, h1640, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1642 | h1642
            · linarith only [h1640, h1642, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1644 | h1644
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1645 | h1645
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1646 | h1646
                  · linarith only [h0, h1471, h1473, h1645, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h1471, h1645, h1646, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1471, h1645, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h1472, h1473, h1644, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1651 | h1651
          · linarith only [h0, h1471, h1473, h1651, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1653 | h1653
            · linarith only [h1651, h1653, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1655 | h1655
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1656 | h1656
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1657 | h1657
                  · linarith only [h0, h1473, h1657, hc12, hlam, hphi, ht01, u0ehi0]
                  · linarith only [h0, h1471, h1656, h1657, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1471, h1656, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h1471, h1473, h1655, hc45, hlam, hphi, ht34, u3ehi1]
    · linarith only [h0, h1471, h1472, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1663 | h1663
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1664 | h1664
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1665 | h1665
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1666 | h1666
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1667 | h1667
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1668 | h1668
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1669 | h1669
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1670 | h1670
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1671 | h1671
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1672 | h1672
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1675 | h1675
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1676 | h1676
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1677 | h1677
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1678 | h1678
                                  · rcases h2bigk with h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c | h1679c
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h0, hlam, p1679_1]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1675, h1678, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1679_1, u3ehi4]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      rcases p1679_3 (m.d 0 2) (by simp) with h1683 | h1683
                                      · rcases p1679_3 (m.d 1 2) (by simp) with h1684 | h1684
                                        · rcases p1679_3 (m.d 2 3) (by simp) with h1685 | h1685
                                          · linarith only [h1663, h1685, hlam]
                                          · linarith only [h1675, h1685, hlam]
                                        · linarith only [h1670, h1684, hlam]
                                      · linarith only [h1683, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      rcases p1679_3 (m.d 0 2) (by simp) with h1690 | h1690
                                      · rcases p1679_3 (m.d 1 2) (by simp) with h1691 | h1691
                                        · rcases p1679_3 (m.d 2 3) (by simp) with h1692 | h1692
                                          · linarith only [h1663, h1692, hlam]
                                          · linarith only [h1676, h1692, hlam]
                                        · linarith only [h1671, h1691, hlam]
                                      · linarith only [h1690, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1679_1, u0ehi1]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1675, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1679_1, u3ehi4]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      rcases p1679_3 (m.d 0 2) (by simp) with h1700 | h1700
                                      · linarith only [h0, h1700, hlam]
                                      · linarith only [h1664, h1700, hlam]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      rcases p1679_3 (m.d 0 2) (by simp) with h1703 | h1703
                                      · linarith only [h0, h1703, hlam]
                                      · linarith only [h1665, h1703, hlam]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1663, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1669, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1663, h1675, h1678, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1679_1, u3ehi4]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h0, h1663, h1676, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1679_1, u3ehi4]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1664, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1670, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1675, hlam, p1679_1]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h0, h1664, h1676, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1679_1, u3ehi4]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1665, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1671, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1676, hlam, p1679_1]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [h1677, hlam, p1679_0]
                                    · have p1679_0 := h1679c.1
                                      have p1679_1 := h1679c.2.1
                                      have p1679_2 := h1679c.2.2.1
                                      have p1679_3 := h1679c.2.2.2
                                      linarith only [hlam, p1679_0]
                                  · linarith only [h0, h1663, h1675, h1677, h1678, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1722 | h1722
                                  · linarith only [h1675, h1677, h1722, hlam]
                                  · rcases h2bigk with h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c | h1724c
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
                                      linarith only [h0, h1675, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1724_1, u3ehi3]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      rcases p1724_3 (m.d 0 2) (by simp) with h1728 | h1728
                                      · rcases p1724_3 (m.d 1 2) (by simp) with h1729 | h1729
                                        · rcases p1724_3 (m.d 2 3) (by simp) with h1730 | h1730
                                          · linarith only [h1663, h1730, hlam]
                                          · linarith only [h1675, h1730, hlam]
                                        · linarith only [h1670, h1729, hlam]
                                      · linarith only [h1728, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      rcases p1724_3 (m.d 0 2) (by simp) with h1735 | h1735
                                      · rcases p1724_3 (m.d 1 2) (by simp) with h1736 | h1736
                                        · rcases p1724_3 (m.d 2 3) (by simp) with h1737 | h1737
                                          · linarith only [h1663, h1737, hlam]
                                          · linarith only [h1676, h1737, hlam]
                                        · linarith only [h1671, h1736, hlam]
                                      · linarith only [h1735, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1724_1, u0ehi1]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1676, h1722, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1724_1, u3ehi3]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      rcases p1724_3 (m.d 0 2) (by simp) with h1745 | h1745
                                      · linarith only [h0, h1745, hlam]
                                      · linarith only [h1664, h1745, hlam]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      rcases p1724_3 (m.d 0 2) (by simp) with h1748 | h1748
                                      · linarith only [h0, h1748, hlam]
                                      · linarith only [h1665, h1748, hlam]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1663, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1669, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1663, h1675, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1724_1, u3ehi3]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h0, h1663, h1675, h1677, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1724_1, u3ehi3]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1664, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1670, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1675, hlam, p1724_1]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1677, hlam, p1724_1]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1665, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1671, hlam, p1724_0]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h1676, hlam, p1724_1]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [h0, h1665, h1675, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1724_1, u3ehi3]
                                    · have p1724_0 := h1724c.1
                                      have p1724_1 := h1724c.2.1
                                      have p1724_2 := h1724c.2.2.1
                                      have p1724_3 := h1724c.2.2.2
                                      linarith only [hlam, p1724_0]
                              · linarith only [h1471, h1667, h1669, h1675, h1676, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1767 | h1767
                              · linarith only [h1675, h1767, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1769 | h1769
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1770 | h1770
                                  · rcases h2bigk with h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c | h1771c
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h0, hlam, p1771_1]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1774 | h1774
                                      · rcases p1771_3 (m.d 1 2) (by simp) with h1775 | h1775
                                        · rcases p1771_3 (m.d 2 3) (by simp) with h1776 | h1776
                                          · linarith only [h1776, hlam, p1771_0]
                                          · rcases p1771_3 (m.d 2 4) (by simp) with h1778 | h1778
                                            · linarith only [h1664, h1778, hlam]
                                            · linarith only [h1675, h1778, hlam]
                                        · linarith only [h1669, h1775, hlam]
                                      · linarith only [h1774, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1783 | h1783
                                      · rcases p1771_3 (m.d 1 2) (by simp) with h1784 | h1784
                                        · rcases p1771_3 (m.d 2 3) (by simp) with h1785 | h1785
                                          · linarith only [h1663, h1785, hlam]
                                          · rcases p1771_3 (m.d 2 4) (by simp) with h1787 | h1787
                                            · linarith only [h1787, hlam, p1771_0]
                                            · rcases p1771_3 (m.d 2 5) (by simp) with h1789 | h1789
                                              · linarith only [h1665, h1789, hlam]
                                              · rcases h3bigk with h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c | h1791c
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1471, hlam, p1791_1]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  rcases p1791_3 (m.d 0 3) (by simp) with h1794 | h1794
                                                  · rcases p1791_3 (m.d 1 3) (by simp) with h1795 | h1795
                                                    · rcases p1791_3 (m.d 2 3) (by simp) with h1796 | h1796
                                                      · linarith only [h1663, h1796, hlam]
                                                      · rcases p1791_3 (m.d 3 4) (by simp) with h1798 | h1798
                                                        · linarith only [h1666, h1798, hlam]
                                                        · linarith only [h1675, h1798, hlam]
                                                    · linarith only [h1669, h1795, hlam]
                                                  · linarith only [h1663, h1794, hlam]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1471, h1669, h1675, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1471, h1669, h1767, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1669, hc12, hlam, hphi, ht01, p1791_1, u0ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  rcases p1791_3 (m.d 0 3) (by simp) with h1807 | h1807
                                                  · linarith only [h1471, h1807, hlam]
                                                  · linarith only [h1663, h1807, hlam]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1669, h1767, h1770, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1669, h1767, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1663, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1669, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1675, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1767, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1666, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1672, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hc34, hlam, hphi, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1471, h1666, h1669, h1767, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1667, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1673, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hc35, hlam, hphi, p1791_1, u3ehi2]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [h1770, hlam, p1791_0]
                                                · have p1791_0 := h1791c.1
                                                  have p1791_1 := h1791c.2.1
                                                  have p1791_2 := h1791c.2.2.1
                                                  have p1791_3 := h1791c.2.2.2
                                                  linarith only [hlam, p1791_0]
                                        · linarith only [h1670, h1784, hlam]
                                      · linarith only [h1783, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1829 | h1829
                                      · rcases p1771_3 (m.d 1 2) (by simp) with h1830 | h1830
                                        · rcases p1771_3 (m.d 2 3) (by simp) with h1831 | h1831
                                          · linarith only [h1663, h1831, hlam]
                                          · rcases p1771_3 (m.d 2 4) (by simp) with h1833 | h1833
                                            · linarith only [h1664, h1833, hlam]
                                            · linarith only [h1769, h1833, hlam]
                                        · linarith only [h1671, h1830, hlam]
                                      · linarith only [h1829, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1771_1, u0ehi1]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1840 | h1840
                                      · linarith only [h0, h1840, hlam]
                                      · linarith only [h1663, h1840, hlam]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1843 | h1843
                                      · linarith only [h0, h1843, hlam]
                                      · linarith only [h1664, h1843, hlam]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      rcases p1771_3 (m.d 0 2) (by simp) with h1846 | h1846
                                      · linarith only [h0, h1846, hlam]
                                      · linarith only [h1665, h1846, hlam]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1663, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1669, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1675, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1767, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1664, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1670, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1664, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1771_1, u3ehi2]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1471, h1666, h1669, h1675, h1767, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1771_1, u3ehi2]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1665, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1671, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h0, h1665, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1771_1, u3ehi2]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [h1769, hlam, p1771_0]
                                    · have p1771_0 := h1771c.1
                                      have p1771_1 := h1771c.2.1
                                      have p1771_2 := h1771c.2.2.1
                                      have p1771_3 := h1771c.2.2.2
                                      linarith only [hlam, p1771_0]
                                  · linarith only [h1675, h1769, h1770, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1865 | h1865
                                  · linarith only [h1471, h1666, h1669, h1675, h1769, h1865, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h1674, h1675, h1865, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1868 | h1868
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1869 | h1869
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1870 | h1870
                                · linarith only [h1670, h1674, h1870, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1872 | h1872
                                  · linarith only [h1670, h1674, h1868, h1872, hlam]
                                  · rcases h2bigk with h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c | h1874c
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, h1869, h1872, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1874_1, u3ehi3]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 2) (by simp) with h1878 | h1878
                                      · rcases p1874_3 (m.d 1 2) (by simp) with h1879 | h1879
                                        · rcases p1874_3 (m.d 2 3) (by simp) with h1880 | h1880
                                          · linarith only [h1663, h1880, hlam]
                                          · linarith only [h1868, h1880, hlam]
                                        · linarith only [h1670, h1879, hlam]
                                      · linarith only [h1878, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 2) (by simp) with h1885 | h1885
                                      · rcases p1874_3 (m.d 1 2) (by simp) with h1886 | h1886
                                        · rcases p1874_3 (m.d 2 3) (by simp) with h1887 | h1887
                                          · linarith only [h1663, h1887, hlam]
                                          · linarith only [h1869, h1887, hlam]
                                        · linarith only [h1671, h1886, hlam]
                                      · linarith only [h1885, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1874_1, u0ehi1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1869, h1872, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1874_1, u3ehi3]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 2) (by simp) with h1895 | h1895
                                      · linarith only [h0, h1895, hlam]
                                      · linarith only [h1664, h1895, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      rcases p1874_3 (m.d 0 2) (by simp) with h1898 | h1898
                                      · linarith only [h0, h1898, hlam]
                                      · linarith only [h1665, h1898, hlam]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1663, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1669, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, h1663, h1868, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1874_1, u3ehi3]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, h1663, h1868, h1870, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1874_1, u3ehi3]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1664, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1670, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1868, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1870, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1665, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1671, hlam, p1874_0]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h1869, hlam, p1874_1]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [h0, h1665, h1868, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1874_1, u3ehi3]
                                    · have p1874_0 := h1874c.1
                                      have p1874_1 := h1874c.2.1
                                      have p1874_2 := h1874c.2.2.1
                                      have p1874_3 := h1874c.2.2.2
                                      linarith only [hlam, p1874_0]
                              · linarith only [h1471, h1666, h1668, h1669, h1673, h1674, h1868, h1869, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1471, h1666, h1668, h1669, h1672, h1674, h1868, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h1471, h1673, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h1471, h1672, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h0, h1671, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h1670, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1669, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1923 | h1923
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1924 | h1924
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1925 | h1925
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1926 | h1926
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1927 | h1927
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1928 | h1928
                          · linarith only [h1668, h1928, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1930 | h1930
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1931 | h1931
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1932 | h1932
                                · linarith only [h1664, h1668, h1932, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1934 | h1934
                                  · linarith only [h1663, h1668, h1930, h1934, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h2bigk with h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c | h1936c
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1931, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi4]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 2) (by simp) with h1940 | h1940
                                      · rcases p1936_3 (m.d 1 2) (by simp) with h1941 | h1941
                                        · rcases p1936_3 (m.d 2 3) (by simp) with h1942 | h1942
                                          · linarith only [h1663, h1942, hlam]
                                          · linarith only [h1930, h1942, hlam]
                                        · linarith only [h1924, h1941, hlam]
                                      · linarith only [h1940, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 2) (by simp) with h1947 | h1947
                                      · rcases p1936_3 (m.d 1 2) (by simp) with h1948 | h1948
                                        · rcases p1936_3 (m.d 2 3) (by simp) with h1949 | h1949
                                          · linarith only [h1663, h1949, hlam]
                                          · linarith only [h1931, h1949, hlam]
                                        · linarith only [h1925, h1948, hlam]
                                      · linarith only [h1947, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, p1936_1, u0ehi1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1931, h1934, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi3]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 2) (by simp) with h1957 | h1957
                                      · linarith only [h0, h1957, hlam]
                                      · linarith only [h1664, h1957, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      rcases p1936_3 (m.d 0 2) (by simp) with h1960 | h1960
                                      · linarith only [h0, h1960, hlam]
                                      · linarith only [h1665, h1960, hlam]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1663, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1923, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1663, h1930, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi3]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1663, h1930, h1932, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi3]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1664, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1924, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1930, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1932, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1665, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1925, hlam, p1936_0]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h1931, hlam, p1936_1]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [h0, h1665, h1930, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1936_1, u3ehi3]
                                    · have p1936_0 := h1936c.1
                                      have p1936_1 := h1936c.2.1
                                      have p1936_2 := h1936c.2.2.1
                                      have p1936_3 := h1936c.2.2.2
                                      linarith only [hlam, p1936_0]
                              · linarith only [h1471, h1667, h1923, h1930, h1931, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1666, h1668, h1930, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h1471, h1667, h1927, hlam]
                      · linarith only [h1471, h1666, h1668, h1926, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h0, h1925, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h1471, h1923, h1924, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1923, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h1666, h1667, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1986 | h1986
            · linarith only [h1666, h1986, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1988 | h1988
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1989 | h1989
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1990 | h1990
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1991 | h1991
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1992 | h1992
                      · linarith only [h1666, h1989, h1992, hc12, hlam, hphi, ht01, u0ehi2]
                      · linarith only [h1471, h1992, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h0, h1665, h1991, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h0, h1664, h1990, hlam]
                · linarith only [h0, h1989, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1998 | h1998
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1999 | h1999
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2000 | h2000
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h2001 | h2001
                      · linarith only [h1471, h1666, h1998, h2001, hc12, hlam, hphi, ht01, u0ehi0]
                      · linarith only [h1471, h2001, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h0, h1665, h2000, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h0, h1664, h1988, h1999, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                · linarith only [h0, h1663, h1998, hc02, hlam, hphi, u0ehi0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2007 | h2007
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2008 | h2008
            · linarith only [h1663, h1665, h2008, hlam]
            · linarith only [h2007, h2008, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2011 | h2011
            · linarith only [h2007, h2011, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2013 | h2013
              · linarith only [h1664, h1665, h2013, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2015 | h2015
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2016 | h2016
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h2017 | h2017
                    · linarith only [h1663, h1665, h2017, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h2017, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h1471, h1664, h2015, h2016, hc02, hlam, hphi, u0ehi0]
                · linarith only [h0, h2015, hc23, hlam, hphi, ht01, ht12, u0ehi0]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2022 | h2022
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2023 | h2023
          · linarith only [h1663, h1664, h2023, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2025 | h2025
            · linarith only [h2023, h2025, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2027 | h2027
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2028 | h2028
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2029 | h2029
                  · linarith only [h1663, h1664, h2029, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h2029, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1663, h2028, hc02, hlam, hphi, u0ehi0]
              · linarith only [h1663, h1664, h2027, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2034 | h2034
          · linarith only [h1663, h1664, h2034, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2036 | h2036
            · linarith only [h2034, h2036, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2038 | h2038
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2039 | h2039
                · rcases m.htr 1 2 4 (by decide) (by decide) with h2040 | h2040
                  · linarith only [h1664, h2040, hc12, hlam, hphi, ht01, u0ehi1]
                  · linarith only [h0, h2040, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h1663, h2039, hc02, hlam, hphi, u0ehi0]
              · linarith only [h1663, h1664, h2038, hc45, hlam, hphi, ht34, u3ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2045 | h2045
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2046 | h2046
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2047 | h2047
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2048 | h2048
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2049 | h2049
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2050 | h2050
                · linarith only [h1663, h2050, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h2050, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2053 | h2053
                · linarith only [h1663, h2053, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h2053, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h2047, h2048, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1663, h2045, h2047, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2058 | h2058
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2059 | h2059
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2060 | h2060
              · linarith only [h2045, h2046, h2060, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2062 | h2062
                · linarith only [h1663, h2062, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h2062, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h2058, h2059, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1663, h2045, h2058, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2067 | h2067
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2068 | h2068
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2069 | h2069
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2070 | h2070
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2071 | h2071
                · linarith only [h0, h1663, h2071, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h2071, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h2045, h2067, h2070, hlam]
            · linarith only [h2068, h2069, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2076 | h2076
            · linarith only [h2068, h2076, hc34, hlam, hphi, u3ehi4]
            · linarith only [h1663, h2067, h2076, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2079 | h2079
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2080 | h2080
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2081 | h2081
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2082 | h2082
                · linarith only [h1663, h2082, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h2082, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2085 | h2085
                · linarith only [h0, h1663, h2085, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h2085, hc23, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h2079, h2080, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h2089 | h2089
            · linarith only [h2079, h2089, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h2091 | h2091
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2092 | h2092
                · linarith only [h0, h1663, h2092, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h2092, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h2095 | h2095
                · linarith only [h0, h1663, h2095, hc12, hlam, hphi, ht01, u0ehi0]
                · linarith only [h0, h2095, hc23, hlam, hphi, ht01, ht12, u0ehi0]

set_option maxHeartbeats 4196000 in
set_option maxHeartbeats 4196000 in
theorem r1l7_10_12_23_L_R_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x0 m hb0 hb2 hb3 h0
  · exact r1l7_10_12_23_L_R_L_I_M_IR_x1 m hb0 hb2 hb3 h0

end R2N4
