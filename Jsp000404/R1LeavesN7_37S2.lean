import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_37S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1471 | h1471
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1472 | h1472
    · linarith only [h1, h1472, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1474 | h1474
      · linarith only [h0, h1, h1474, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1476 | h1476
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1477 | h1477
          · linarith only [h0, h1, h1477, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1479 | h1479
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1480 | h1480
              · linarith only [h0, h1, h1476, h1480, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1482 | h1482
                · linarith only [h0, h1, h1474, h1482, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1484 | h1484
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1485 | h1485
                    · linarith only [h0, h1472, h1477, h1485, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1487 | h1487
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1488 | h1488
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
                          · linarith only [h0, h1484, h1489, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h0, h1472, h1484, h1489, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1, h1484, h1488, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h1484, h1487, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h1476, h1482, h1484, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h1476, h1479, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1496 | h1496
          · linarith only [h1, h1471, h1476, h1496, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1498 | h1498
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1499 | h1499
              · linarith only [h1, h1471, h1499, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
                · linarith only [h0, h1, h1474, h1501, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h0, h1476, h1503, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1505 | h1505
                    · linarith only [h0, h1476, h1496, h1505, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1507 | h1507
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1508 | h1508
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1509 | h1509
                          · linarith only [h1471, h1472, h1499, h1509, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1511 | h1511
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1512 | h1512
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1513 | h1513
                                · linarith only [h1471, h1472, h1503, h1509, h1511, h1513, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1515 | h1515
                                  · linarith only [h1471, h1476, h1507, h1513, h1515, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h1bigk with h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c | h1517c
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1472, h1505, h1513, hc12, hc45, hlam, hphi, ht23, ht34, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1, hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1472, h1505, h1513, hc14, hc45, hlam, hphi, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1472, hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h0, hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1501, hlam, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1503, hlam, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1505, hlam, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h0, h1501, hc12, hc23, hlam, hphi, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      rcases p1517_3 (m.d 0 1) (by simp) with h1529 | h1529
                                      · linarith only [h1, h1529, hlam]
                                      · linarith only [h0, h1529, hlam]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      rcases p1517_3 (m.d 0 1) (by simp) with h1533 | h1533
                                      · linarith only [h1, h1533, hlam]
                                      · linarith only [h1471, h1533, hlam]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1472, h1501, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1517_1, u5ehi0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1471, hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1, h1471, h1501, hc12, hc23, hlam, hphi, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1507, hlam, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1509, hlam, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1471, h1503, h1505, h1513, hc12, hc45, hlam, hphi, ht23, ht34, p1517_1]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      rcases p1517_3 (m.d 0 1) (by simp) with h1543 | h1543
                                      · linarith only [h1472, h1543, hlam]
                                      · linarith only [h0, h1543, hlam]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [h1508, hlam, p1517_0]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      rcases p1517_3 (m.d 0 1) (by simp) with h1547 | h1547
                                      · linarith only [h1472, h1547, hlam]
                                      · linarith only [h1471, h1547, hlam]
                                    · have p1517_0 := h1517c.1
                                      have p1517_1 := h1517c.2.1
                                      have p1517_2 := h1517c.2.2.1
                                      have p1517_3 := h1517c.2.2.2
                                      linarith only [hlam, p1517_0]
                              · linarith only [h1, h1471, h1501, h1503, h1512, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1501, h1508, h1511, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · linarith only [h1, h1471, h1503, h1508, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h1471, h1503, h1507, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1471, h1498, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1556 | h1556
    · linarith only [h1, h1556, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1558 | h1558
      · linarith only [h0, h1, h1558, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1560 | h1560
        · linarith only [h0, h1471, h1560, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1562 | h1562
          · linarith only [h0, h1, h1562, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1564 | h1564
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1565 | h1565
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1566 | h1566
                · linarith only [h0, h1, h1558, h1566, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1568 | h1568
                  · linarith only [h0, h1560, h1565, h1568, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1570 | h1570
                    · linarith only [h0, h1, h1562, h1566, h1570, hc02, hc23, hlam, hphi]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1572 | h1572
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1573 | h1573
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1574 | h1574
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1575 | h1575
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1576 | h1576
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1577 | h1577
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1578 | h1578
                                  · linarith only [h1564, h1578, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h1bigk with h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c | h1580c
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1556, h1566, h1572, h1574, hc12, hc23, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1471, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1556, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1566, hlam, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1568, hlam, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1570, hlam, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, h1566, hc12, hc23, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      rcases p1580_3 (m.d 0 1) (by simp) with h1592 | h1592
                                      · linarith only [h1, h1592, hlam]
                                      · linarith only [h0, h1592, hlam]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1566, h1574, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1580_1, u5ehi1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, h1556, h1566, hc12, hc23, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, h1568, hc12, hc24, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      rcases p1580_3 (m.d 0 1) (by simp) with h1599 | h1599
                                      · linarith only [h1471, h1599, hlam]
                                      · linarith only [h0, h1599, hlam]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1572, hlam, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, h1556, h1566, h1572, hc12, hc23, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h0, h1570, hc12, hc25, hlam, hphi, p1580_1]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      rcases p1580_3 (m.d 0 1) (by simp) with h1606 | h1606
                                      · linarith only [h1556, h1606, hlam]
                                      · linarith only [h0, h1606, hlam]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1573, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [h1574, hlam, p1580_0]
                                    · have p1580_0 := h1580c.1
                                      have p1580_1 := h1580c.2.1
                                      have p1580_2 := h1580c.2.2.1
                                      have p1580_3 := h1580c.2.2.2
                                      linarith only [hlam, p1580_0]
                                · linarith only [h0, h1471, h1560, h1565, h1566, h1572, h1577, hc12, hc23, hlam, hphi]
                              · linarith only [h1471, h1565, h1566, h1572, h1576, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                            · linarith only [h1471, h1565, h1566, h1572, h1575, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · linarith only [h1471, h1565, h1574, hlam]
                        · linarith only [h1471, h1565, h1572, h1573, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                      · linarith only [h1, h1564, h1572, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1618 | h1618
                · linarith only [h0, h1471, h1565, h1618, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1620 | h1620
                  · linarith only [h0, h1560, h1620, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1622 | h1622
                    · linarith only [h0, h1622, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1624 | h1624
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1626 | h1626
                          · linarith only [h0, h1471, h1565, h1618, h1624, h1626, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1471, h1626, hc12, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h0, h1, h1625, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h1624, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1631 | h1631
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1632 | h1632
                · linarith only [h0, h1558, h1632, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1634 | h1634
                  · linarith only [h0, h1560, h1634, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1636 | h1636
                    · linarith only [h0, h1, h1564, h1636, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1638 | h1638
                      · linarith only [h1564, h1631, h1638, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                      · linarith only [h0, h1, h1638, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
                · linarith only [h0, h1471, h1631, h1641, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1643 | h1643
                  · linarith only [h0, h1, h1560, h1564, h1631, h1643, hc02, hc45, hlam, hphi, ht23, ht34]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1645 | h1645
                    · linarith only [h0, h1, h1564, h1631, h1645, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1647 | h1647
                      · linarith only [h0, h1, h1564, h1641, h1647, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1, h1647, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1651 | h1651
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1652 | h1652
    · linarith only [h0, h1652, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1654 | h1654
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1655 | h1655
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1656 | h1656
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1657 | h1657
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1658 | h1658
              · linarith only [h0, h1650, h1657, h1658, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1660 | h1660
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1661 | h1661
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1662 | h1662
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1663 | h1663
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1664 | h1664
                        · linarith only [h1650, h1652, h1662, h1664, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1666 | h1666
                          · linarith only [h1650, h1652, h1658, h1663, h1664, h1666, hc04, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h1650, h1652, h1663, h1666, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1669 | h1669
                        · linarith only [h1650, h1652, h1657, h1662, h1663, h1669, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · linarith only [h1650, h1652, h1657, h1660, h1663, h1669, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h1650, h1656, h1657, h1662, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1655, h1661, hlam]
                · linarith only [h0, h1656, h1660, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1675 | h1675
              · linarith only [h1651, h1652, h1675, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1677 | h1677
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1678 | h1678
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1679 | h1679
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1680 | h1680
                      · linarith only [h1650, h1652, h1657, h1679, h1680, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1682 | h1682
                        · linarith only [h1650, h1652, h1679, h1682, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1684 | h1684
                          · linarith only [h1651, h1652, h1682, h1684, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1686 | h1686
                            · linarith only [h1654, h1657, h1686, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1688 | h1688
                              · linarith only [h0, h1654, h1688, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1690 | h1690
                                · linarith only [h1651, h1652, h1678, h1684, h1690, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1692 | h1692
                                  · linarith only [h1651, h1652, h1678, h1684, h1686, h1692, hc23, hc34, hlam, hphi]
                                  · rcases h1bigk with h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c | h1694c
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h0, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1652, h1677, h1682, hc23, hc35, hlam, hphi, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1652, h1678, h1682, h1686, hc23, hc35, hlam, hphi, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1652, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      rcases p1694_3 (m.d 0 1) (by simp) with h1700 | h1700
                                      · linarith only [h1700, hlam, p1694_0]
                                      · rcases p1694_3 (m.d 1 2) (by simp) with h1702 | h1702
                                        · rcases p1694_3 (m.d 1 3) (by simp) with h1703 | h1703
                                          · linarith only [h1677, h1703, hlam]
                                          · rcases p1694_3 (m.d 1 4) (by simp) with h1705 | h1705
                                            · linarith only [h1678, h1705, hlam]
                                            · rcases p1694_3 (m.d 1 5) (by simp) with h1707 | h1707
                                              · linarith only [h1679, h1707, hlam]
                                              · linarith only [h1652, h1707, hlam]
                                        · linarith only [h1702, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      rcases p1694_3 (m.d 0 1) (by simp) with h1712 | h1712
                                      · linarith only [h0, h1712, hlam]
                                      · linarith only [h1650, h1712, hlam]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      rcases p1694_3 (m.d 0 1) (by simp) with h1715 | h1715
                                      · linarith only [h0, h1715, hlam]
                                      · linarith only [h1651, h1715, hlam]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1694_1, u5ehi1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1650, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1677, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1680, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1682, hlam, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1651, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1678, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h0, h1651, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1684, hlam, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1650, h1677, h1682, h1692, hc23, hc45, hlam, hphi, ht34, p1694_1]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [h1679, hlam, p1694_0]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      rcases p1694_3 (m.d 0 1) (by simp) with h1731 | h1731
                                      · linarith only [h1652, h1731, hlam]
                                      · linarith only [h1650, h1731, hlam]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      rcases p1694_3 (m.d 0 1) (by simp) with h1734 | h1734
                                      · linarith only [h1652, h1734, hlam]
                                      · linarith only [h1651, h1734, hlam]
                                    · have p1694_0 := h1694c.1
                                      have p1694_1 := h1694c.2.1
                                      have p1694_2 := h1694c.2.2.1
                                      have p1694_3 := h1694c.2.2.2
                                      linarith only [hlam, p1694_0]
                    · linarith only [h0, h1656, h1679, hlam]
                  · linarith only [h0, h1655, h1656, h1678, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1656, h1677, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1741 | h1741
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1742 | h1742
              · linarith only [h0, h1650, h1741, h1742, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1744 | h1744
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1745 | h1745
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1746 | h1746
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1747 | h1747
                      · linarith only [h0, h1650, h1656, h1746, h1747, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1650, h1656, h1741, h1746, h1747, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1750 | h1750
                      · linarith only [h0, h1650, h1746, h1750, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1650, h1741, h1744, h1746, h1750, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h1651, h1655, h1745, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1654, h1744, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1755 | h1755
              · linarith only [h0, h1651, h1755, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1757 | h1757
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1758 | h1758
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1759 | h1759
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1760 | h1760
                      · linarith only [h0, h1650, h1656, h1759, h1760, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1762 | h1762
                        · linarith only [h0, h1651, h1656, h1759, h1760, h1762, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1764 | h1764
                          · linarith only [h0, h1651, h1656, h1741, h1755, h1759, h1764, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1766 | h1766
                            · linarith only [h1650, h1741, h1757, h1766, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1768 | h1768
                              · linarith only [h0, h1650, h1656, h1741, h1757, h1759, h1762, h1768, hc01, hc34, hlam, hphi, ht12, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1770 | h1770
                                · linarith only [h0, h1651, h1656, h1758, h1759, h1764, h1770, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1772 | h1772
                                  · linarith only [h0, h1651, h1656, h1758, h1759, h1764, h1766, h1772, hc23, hc34, hlam, hphi]
                                  · rcases h1bigk with h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c | h1774c
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1656, h1757, h1759, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1656, h1759, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1652, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      rcases p1774_3 (m.d 0 1) (by simp) with h1780 | h1780
                                      · linarith only [h1780, hlam, p1774_0]
                                      · rcases p1774_3 (m.d 1 2) (by simp) with h1782 | h1782
                                        · rcases p1774_3 (m.d 1 3) (by simp) with h1783 | h1783
                                          · linarith only [h1757, h1783, hlam]
                                          · rcases p1774_3 (m.d 1 4) (by simp) with h1785 | h1785
                                            · linarith only [h1758, h1785, hlam]
                                            · rcases p1774_3 (m.d 1 5) (by simp) with h1787 | h1787
                                              · linarith only [h1759, h1787, hlam]
                                              · linarith only [h1652, h1787, hlam]
                                        · linarith only [h1782, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1650, h1656, h1759, hlam, p1774_2]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1651, h1656, h1759, hlam, p1774_2]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1656, h1759, hc01, hc12, hlam, hphi, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1650, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1757, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1760, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1762, hlam, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1651, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1758, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h0, h1651, h1656, h1759, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1764, hlam, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1651, h1762, h1772, hc14, hc45, hlam, hphi, p1774_1]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [h1759, hlam, p1774_0]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      rcases p1774_3 (m.d 0 1) (by simp) with h1807 | h1807
                                      · linarith only [h1652, h1807, hlam]
                                      · linarith only [h1650, h1807, hlam]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      rcases p1774_3 (m.d 0 1) (by simp) with h1810 | h1810
                                      · linarith only [h1652, h1810, hlam]
                                      · linarith only [h1651, h1810, hlam]
                                    · have p1774_0 := h1774c.1
                                      have p1774_1 := h1774c.2.1
                                      have p1774_2 := h1774c.2.2.1
                                      have p1774_3 := h1774c.2.2.2
                                      linarith only [hlam, p1774_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1814 | h1814
                      · linarith only [h0, h1650, h1759, h1814, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1816 | h1816
                        · linarith only [h0, h1651, h1759, h1814, h1816, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1818 | h1818
                          · linarith only [h0, h1651, h1759, h1818, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1820 | h1820
                            · linarith only [h1650, h1741, h1757, h1820, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1822 | h1822
                              · linarith only [h0, h1651, h1757, h1759, h1814, h1816, h1822, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
                              · linarith only [h0, h1651, h1757, h1759, h1814, h1822, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h1650, h1655, h1757, h1758, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1654, h1757, hlam]
        · linarith only [h0, h1651, h1655, hlam]
      · linarith only [h0, h1650, h1654, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1829 | h1829
    · linarith only [h0, h1829, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1831 | h1831
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1832 | h1832
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1833 | h1833
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1834 | h1834
            · linarith only [h1650, h1651, h1834, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1836 | h1836
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1837 | h1837
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1838 | h1838
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1839 | h1839
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1840 | h1840
                      · linarith only [h1650, h1651, h1834, h1838, h1840, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1842 | h1842
                        · linarith only [h1650, h1651, h1840, h1842, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1844 | h1844
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1845 | h1845
                            · linarith only [h1650, h1829, h1837, h1840, h1844, h1845, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1847 | h1847
                              · linarith only [h1650, h1829, h1837, h1842, h1847, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h1849 | h1849
                                · linarith only [h1832, h1849, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h1851 | h1851
                                  · rcases h1bigk with h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h0, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1829, h1840, h1844, hc13, hc34, hlam, hphi, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1651, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1829, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      rcases p1852_3 (m.d 0 1) (by simp) with h1858 | h1858
                                      · linarith only [h1858, hlam, p1852_0]
                                      · rcases p1852_3 (m.d 1 2) (by simp) with h1860 | h1860
                                        · rcases p1852_3 (m.d 1 3) (by simp) with h1861 | h1861
                                          · linarith only [h1837, h1861, hlam]
                                          · rcases p1852_3 (m.d 1 4) (by simp) with h1863 | h1863
                                            · linarith only [h1838, h1863, hlam]
                                            · linarith only [h1651, h1863, hlam]
                                        · linarith only [h1860, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      rcases p1852_3 (m.d 0 1) (by simp) with h1868 | h1868
                                      · linarith only [h0, h1868, hlam]
                                      · linarith only [h1650, h1868, hlam]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1844, hc12, hlam, hphi, ht01, ht0b, ht5b, p1852_1, u5ehi1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1829, hc01, hc12, hlam, hphi, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1650, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1837, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1840, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1842, hlam, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1650, h1837, h1840, hc23, hc34, hlam, hphi, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1838, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      rcases p1852_3 (m.d 0 1) (by simp) with h1880 | h1880
                                      · linarith only [h1651, h1880, hlam]
                                      · linarith only [h1650, h1880, hlam]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1650, h1829, h1837, h1840, hc23, hc34, hlam, hphi, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1650, h1837, h1842, hc23, hc35, hlam, hphi, p1852_1]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1839, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      rcases p1852_3 (m.d 0 1) (by simp) with h1887 | h1887
                                      · linarith only [h1829, h1887, hlam]
                                      · linarith only [h1650, h1887, hlam]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [h1844, hlam, p1852_0]
                                    · have p1852_0 := h1852c.1
                                      have p1852_1 := h1852c.2.1
                                      have p1852_2 := h1852c.2.2.1
                                      have p1852_3 := h1852c.2.2.2
                                      linarith only [hlam, p1852_0]
                                  · linarith only [h1651, h1836, h1840, h1851, hlam]
                          · linarith only [h1651, h1836, h1844, hlam]
                    · linarith only [h0, h1832, h1836, h1839, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · linarith only [h0, h1832, h1836, h1838, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h1832, h1836, h1837, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1897 | h1897
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1898 | h1898
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1899 | h1899
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1900 | h1900
                      · linarith only [h1650, h1834, h1900, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1902 | h1902
                        · linarith only [h1650, h1651, h1836, h1902, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                          · linarith only [h1650, h1651, h1836, h1900, h1904, hc13, hc34, hlam, hphi]
                          · linarith only [h1650, h1651, h1897, h1904, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1833, h1899, hlam]
                  · linarith only [h0, h1832, h1833, h1898, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1833, h1897, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1910 | h1910
            · linarith only [h1650, h1651, h1910, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1912 | h1912
              · linarith only [h1832, h1833, h1912, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1914 | h1914
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1915 | h1915
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1916 | h1916
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1917 | h1917
                      · linarith only [h1650, h1651, h1832, h1833, h1910, h1916, h1917, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1919 | h1919
                        · linarith only [h1650, h1651, h1832, h1833, h1916, h1919, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1921 | h1921
                          · linarith only [h1650, h1651, h1912, h1914, h1917, h1921, hc23, hc34, hlam, hphi]
                          · linarith only [h1650, h1651, h1914, h1921, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1924 | h1924
                      · linarith only [h1650, h1651, h1915, h1916, h1924, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1926 | h1926
                        · linarith only [h1650, h1651, h1915, h1916, h1926, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1928 | h1928
                          · linarith only [h1915, h1916, h1928, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                          · linarith only [h1650, h1651, h1914, h1928, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1832, h1915, hlam]
                · linarith only [h0, h1831, h1914, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1933 | h1933
          · linarith only [h1832, h1933, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1935 | h1935
            · linarith only [h0, h1650, h1832, h1935, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1937 | h1937
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1938 | h1938
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1939 | h1939
                  · linarith only [h1832, h1937, h1939, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1941 | h1941
                    · linarith only [h0, h1650, h1933, h1938, h1939, h1941, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1943 | h1943
                      · linarith only [h1650, h1935, h1937, h1943, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1945 | h1945
                        · linarith only [h0, h1650, h1939, h1945, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1947 | h1947
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1948 | h1948
                            · linarith only [h1651, h1937, h1943, h1948, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                            · linarith only [h0, h1650, h1939, h1948, hc13, hc34, hlam, hphi]
                          · linarith only [h1651, h1937, h1947, hlam]
                · linarith only [h0, h1650, h1831, h1933, h1938, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1953 | h1953
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1954 | h1954
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1955 | h1955
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1956 | h1956
                      · linarith only [h0, h1650, h1832, h1954, h1956, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1958 | h1958
                        · linarith only [h0, h1650, h1832, h1954, h1958, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1960 | h1960
                          · linarith only [h1650, h1651, h1937, h1956, h1960, hc13, hc34, hlam, hphi]
                          · linarith only [h1650, h1651, h1953, h1960, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h1650, h1832, h1953, h1954, h1955, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1964 | h1964
                    · linarith only [h1954, h1964, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h1966 | h1966
                      · linarith only [h0, h1650, h1954, h1966, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h1968 | h1968
                        · linarith only [h0, h1650, h1954, h1968, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h1970 | h1970
                          · linarith only [h0, h1650, h1832, h1937, h1953, h1966, h1970, hc23, hc34, hlam, hphi]
                          · linarith only [h1650, h1651, h1953, h1970, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1831, h1953, hlam]
      · linarith only [h0, h1650, h1831, hlam]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1976 | h1976
  · linarith only [h1650, h1976, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1978 | h1978
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1979 | h1979
      · rcases m.htr 0 2 5 (by decide) (by decide) with h1980 | h1980
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1981 | h1981
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1982 | h1982
            · linarith only [h0, h1975, h1982, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1984 | h1984
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1985 | h1985
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1986 | h1986
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1987 | h1987
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1988 | h1988
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h1989 | h1989
                        · linarith only [h1975, h1976, h1982, h1984, h1988, h1989, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h1991 | h1991
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h1992 | h1992
                            · linarith only [h1978, h1992, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h1994 | h1994
                              · linarith only [h1975, h1976, h1985, h1989, h1994, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1996 | h1996
                                · linarith only [h1976, h1984, h1988, h1989, h1991, h1992, h1996, hc01, hc12, hlam, hphi]
                                · rcases h1bigk with h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c | h1998c
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h0, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1650, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1976, h1985, h1989, h1991, hc34, hc45, hlam, hphi, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1976, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    rcases p1998_3 (m.d 0 1) (by simp) with h2004 | h2004
                                    · linarith only [h2004, hlam, p1998_0]
                                    · rcases p1998_3 (m.d 1 2) (by simp) with h2006 | h2006
                                      · rcases p1998_3 (m.d 1 3) (by simp) with h2007 | h2007
                                        · linarith only [h1984, h2007, hlam]
                                        · linarith only [h1650, h2007, hlam]
                                      · linarith only [h2006, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1988, h1992, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    rcases p1998_3 (m.d 0 1) (by simp) with h2013 | h2013
                                    · linarith only [h0, h2013, hlam]
                                    · linarith only [h1975, h2013, hlam]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1976, hc12, hlam, hphi, ht01, ht0b, ht5b, p1998_1, u5ehi0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    rcases p1998_3 (m.d 0 1) (by simp) with h2017 | h2017
                                    · linarith only [h2017, hlam, p1998_0]
                                    · rcases p1998_3 (m.d 1 2) (by simp) with h2019 | h2019
                                      · rcases p1998_3 (m.d 1 3) (by simp) with h2020 | h2020
                                        · rcases p1998_3 (m.d 1 4) (by simp) with h2021 | h2021
                                          · linarith only [h1987, h2021, hlam]
                                          · rcases p1998_3 (m.d 1 5) (by simp) with h2023 | h2023
                                            · linarith only [h1988, h2023, hlam]
                                            · linarith only [h1976, h2023, hlam]
                                        · linarith only [h2020, hlam, p1998_0]
                                      · linarith only [h0, h2019, hlam]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1984, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    rcases p1998_3 (m.d 0 1) (by simp) with h2030 | h2030
                                    · linarith only [h1650, h2030, hlam]
                                    · linarith only [h1975, h2030, hlam]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1976, h1984, hc01, hc12, hlam, hphi, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1975, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1985, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1987, hlam, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1989, hlam, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1975, h1985, h1989, h1991, hc34, hc45, hlam, hphi, p1998_1]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1986, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [h1988, hlam, p1998_0]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    rcases p1998_3 (m.d 0 1) (by simp) with h2042 | h2042
                                    · linarith only [h1976, h2042, hlam]
                                    · linarith only [h1975, h2042, hlam]
                                  · have p1998_0 := h1998c.1
                                    have p1998_1 := h1998c.2.1
                                    have p1998_2 := h1998c.2.2.1
                                    have p1998_3 := h1998c.2.2.2
                                    linarith only [hlam, p1998_0]
                          · linarith only [h1975, h1976, h1987, h1989, h1991, hc23, hc45, hlam, hphi, ht34]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2047 | h2047
                        · linarith only [h1650, h1975, h1988, h2047, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2049 | h2049
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2050 | h2050
                            · linarith only [h1650, h1988, h2050, hc01, hc23, hlam, hphi, ht12]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2052 | h2052
                              · linarith only [h1975, h1985, h2047, h2052, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2054 | h2054
                                · linarith only [h1650, h1975, h1985, h1988, h2047, h2049, h2054, hlam]
                                · linarith only [h1650, h1975, h1988, h2054, hc14, hc45, hlam, hphi]
                          · linarith only [h1650, h1981, h1988, h2049, hc23, hc35, hlam, hphi]
                    · linarith only [h1650, h1975, h1981, h1987, hlam]
                  · linarith only [h0, h1980, h1986, hlam]
                · linarith only [h0, h1980, h1985, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h0, h1980, h1984, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · linarith only [h1650, h1975, h1981, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2063 | h2063
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2064 | h2064
            · linarith only [h1650, h1975, h2064, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2066 | h2066
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2067 | h2067
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2068 | h2068
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2069 | h2069
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2070 | h2070
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2071 | h2071
                        · linarith only [h1650, h1975, h1978, h1980, h2064, h2068, h2071, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2073 | h2073
                          · linarith only [h1978, h1980, h2068, h2073, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1978, h1980, h2063, h2068, h2073, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2076 | h2076
                        · linarith only [h1650, h1975, h1978, h1980, h2068, h2076, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2078 | h2078
                          · linarith only [h1978, h1980, h2068, h2078, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h1978, h1980, h2063, h2068, h2078, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h1650, h1975, h2063, h2069, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2082 | h2082
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2083 | h2083
                      · linarith only [h2066, h2068, h2083, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2085 | h2085
                        · linarith only [h1650, h1975, h2066, h2068, h2085, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2087 | h2087
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2088 | h2088
                            · linarith only [h1650, h1978, h2083, h2088, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2090 | h2090
                              · linarith only [h1975, h1976, h2067, h2085, h2090, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                              · linarith only [h1650, h1975, h2066, h2067, h2068, h2087, h2090, hc34, hc45, hlam, hphi]
                          · linarith only [h0, h1975, h2068, h2082, h2087, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h1650, h1978, h2063, h2068, h2082, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h1650, h1975, h1979, h1980, h2066, h2067, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1978, h2066, hlam]
          · linarith only [h1650, h1975, h2063, hlam]
      · linarith only [h0, h1975, h1979, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2099 | h2099
      · rcases m.htr 0 2 5 (by decide) (by decide) with h2100 | h2100
        · linarith only [h1978, h2100, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h2102 | h2102
          · rcases m.htr 0 4 5 (by decide) (by decide) with h2103 | h2103
            · linarith only [h0, h1975, h2103, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2105 | h2105
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2106 | h2106
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2107 | h2107
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2108 | h2108
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2109 | h2109
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2110 | h2110
                        · linarith only [h0, h1975, h1978, h2103, h2105, h2110, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2112 | h2112
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2113 | h2113
                            · linarith only [h2105, h2113, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                            · linarith only [h0, h1978, h2105, h2109, h2113, hc01, hc12, hlam, hphi]
                          · linarith only [h1978, h2102, h2112, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2117 | h2117
                        · linarith only [h1975, h2117, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2119 | h2119
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2120 | h2120
                            · linarith only [h2105, h2109, h2120, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2122 | h2122
                              · linarith only [h0, h1975, h1978, h2105, h2106, h2109, h2117, h2122, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h2124 | h2124
                                · linarith only [h0, h1975, h1978, h2105, h2106, h2109, h2117, h2119, h2124, hlam]
                                · linarith only [h0, h1975, h1978, h2105, h2109, h2124, hc14, hc45, hlam, hphi]
                          · linarith only [h1978, h2102, h2119, hlam]
                    · linarith only [h0, h1975, h1978, h2102, h2105, h2108, hlam]
                  · linarith only [h0, h1975, h1978, h2105, h2106, h2107, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h1975, h1978, h2105, h2106, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2131 | h2131
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2132 | h2132
                  · linarith only [h2105, h2132, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2134 | h2134
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2135 | h2135
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2136 | h2136
                        · linarith only [h1975, h2136, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2138 | h2138
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2139 | h2139
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h2140 | h2140
                              · linarith only [h0, h1975, h2131, h2132, h2136, h2140, hlam]
                              · linarith only [h0, h1975, h2132, h2140, hc14, hc45, hlam, hphi]
                            · linarith only [h2105, h2135, h2139, hlam]
                          · linarith only [h2105, h2135, h2138, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h2145 | h2145
                        · linarith only [h0, h1975, h2105, h2135, h2145, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h2147 | h2147
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h2148 | h2148
                            · linarith only [h0, h1975, h2105, h2131, h2135, h2147, h2148, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h1975, h2105, h2131, h2147, h2148, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h0, h1975, h2105, h2131, h2147, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1975, h2102, h2105, h2134, hlam]
                · linarith only [h0, h2099, h2131, hlam]
          · linarith only [h1650, h1975, h2102, hlam]
      · linarith only [h0, h1975, h2099, hlam]

set_option maxHeartbeats 7470000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_R_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1650 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1975 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2156 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1bigk := hb1.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5ehi := hb5.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  linarith only [h1975, h2156, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]

end R2N4
