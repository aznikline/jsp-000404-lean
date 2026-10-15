import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7634000 in
theorem r1l7_10_12_13_25_L_0_L_I_L_I_M_IR_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1494 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1495 | h1495
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1496 | h1496
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1497 | h1497
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1498 | h1498
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1499 | h1499
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1500 | h1500
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1501 | h1501
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1502 | h1502
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1503 | h1503
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1504 | h1504
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1505 | h1505
                      · linarith only [h1494, h1505, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · linarith only [h1499, h1504, h1505, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1508 | h1508
                      · linarith only [h0, h1494, h1498, h1504, h1508, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1510 | h1510
                        · linarith only [h1501, h1504, h1510, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1512 | h1512
                          · linarith only [h1501, h1508, h1512, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1514 | h1514
                            · linarith only [h1496, h1514, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1516 | h1516
                              · linarith only [h0, h1494, h1498, h1510, h1514, h1516, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h1500, h1504, h1516, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1494, h1497, h1498, h1503, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                · linarith only [h0, h1494, h1498, h1500, h1502, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
              · linarith only [h0, h1494, h1498, h1500, h1501, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1522 | h1522
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1523 | h1523
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1524 | h1524
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1525 | h1525
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1526 | h1526
                      · linarith only [h1494, h1526, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · linarith only [h0, h1494, h1499, h1525, h1526, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1529 | h1529
                      · linarith only [h0, h1494, h1529, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1531 | h1531
                        · linarith only [h1522, h1525, h1531, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1533 | h1533
                          · linarith only [h0, h1494, h1498, h1522, h1525, h1529, h1533, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1535 | h1535
                            · linarith only [h1496, h1500, h1535, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1537 | h1537
                              · linarith only [h1498, h1500, h1537, hlam]
                              · rcases h2bigk with h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c | h1539c
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h0, hlam, p1539_1]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  rcases p1539_3 (m.d 0 2) (by simp) with h1542 | h1542
                                  · rcases p1539_3 (m.d 1 2) (by simp) with h1543 | h1543
                                    · rcases p1539_3 (m.d 2 3) (by simp) with h1544 | h1544
                                      · linarith only [h1544, hlam, p1539_0]
                                      · rcases p1539_3 (m.d 2 4) (by simp) with h1546 | h1546
                                        · linarith only [h1496, h1546, hlam]
                                        · linarith only [h1531, h1546, hlam]
                                    · linarith only [h1522, h1543, hlam]
                                  · linarith only [h1542, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  rcases p1539_3 (m.d 0 2) (by simp) with h1551 | h1551
                                  · rcases p1539_3 (m.d 1 2) (by simp) with h1552 | h1552
                                    · rcases p1539_3 (m.d 2 3) (by simp) with h1553 | h1553
                                      · linarith only [h1495, h1553, hlam]
                                      · rcases p1539_3 (m.d 2 4) (by simp) with h1555 | h1555
                                        · linarith only [h1555, hlam, p1539_0]
                                        · rcases p1539_3 (m.d 2 5) (by simp) with h1557 | h1557
                                          · linarith only [h1497, h1557, hlam]
                                          · linarith only [h1535, h1557, hlam]
                                    · linarith only [h1523, h1552, hlam]
                                  · linarith only [h1551, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1539_1, u0elo1, u5ehi2]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h0, h1494, h1499, h1522, h1525, h1537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1539_1]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h0, h1494, h1499, h1522, h1525, h1537, hlam, p1539_2]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  rcases p1539_3 (m.d 0 2) (by simp) with h1566 | h1566
                                  · linarith only [h0, h1566, hlam]
                                  · linarith only [h1496, h1566, hlam]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  rcases p1539_3 (m.d 0 2) (by simp) with h1569 | h1569
                                  · linarith only [h0, h1569, hlam]
                                  · linarith only [h1497, h1569, hlam]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1495, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1522, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1531, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1533, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1496, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1523, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1539_1, u0elo1]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1535, hlam, p1539_1]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1497, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1524, hlam, p1539_0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1539_1, u0elo1]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [h1494, h1499, h1524, h1529, hc24, hlam, hphi, ht0b, ht45, ht5b, p1539_1, u0elo0]
                                · have p1539_0 := h1539c.1
                                  have p1539_1 := h1539c.2.1
                                  have p1539_2 := h1539c.2.2.1
                                  have p1539_3 := h1539c.2.2.2
                                  linarith only [hlam, p1539_0]
                  · linarith only [h0, h1494, h1497, h1499, h1524, hlam, hphi, ht0b, ht5b, u0elo4, u5ehi3]
                · linarith only [h0, h1494, h1499, h1523, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h1494, h1499, h1522, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1590 | h1590
            · linarith only [h1498, h1499, h1590, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1592 | h1592
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1593 | h1593
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1594 | h1594
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1595 | h1595
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1596 | h1596
                      · linarith only [h1494, h1499, h1596, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1598 | h1598
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1599 | h1599
                          · linarith only [h1494, h1499, h1592, h1599, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1601 | h1601
                            · linarith only [h0, h1494, h1590, h1593, h1595, h1601, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1603 | h1603
                              · linarith only [h1496, h1590, h1598, h1603, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi0]
                              · rcases h2bigk with h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c | h1605c
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h0, hlam, p1605_1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1598, hc34, hlam, hphi, ht0b, ht45, ht5b, p1605_1, u0elo1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  rcases p1605_3 (m.d 0 2) (by simp) with h1609 | h1609
                                  · rcases p1605_3 (m.d 1 2) (by simp) with h1610 | h1610
                                    · rcases p1605_3 (m.d 2 3) (by simp) with h1611 | h1611
                                      · linarith only [h1495, h1611, hlam]
                                      · linarith only [h1598, h1611, hlam]
                                    · linarith only [h1593, h1610, hlam]
                                  · linarith only [h1609, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1598, h1599, hc34, hlam, hphi, ht0b, ht45, ht5b, p1605_1, u0elo1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1495, h1598, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1605_1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  rcases p1605_3 (m.d 0 2) (by simp) with h1619 | h1619
                                  · linarith only [h0, h1619, hlam]
                                  · linarith only [h1495, h1619, hlam]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  rcases p1605_3 (m.d 0 2) (by simp) with h1622 | h1622
                                  · linarith only [h0, h1622, hlam]
                                  · linarith only [h1496, h1622, hlam]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  rcases p1605_3 (m.d 0 2) (by simp) with h1625 | h1625
                                  · linarith only [h0, h1625, hlam]
                                  · linarith only [h1497, h1625, hlam]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1495, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1592, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1494, h1592, hc24, hlam, hphi, ht0b, ht45, ht5b, p1605_1, u0elo0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1599, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1496, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1593, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1598, hlam, p1605_1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1601, hlam, p1605_1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1497, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1594, hlam, p1605_0]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1605_1, u0elo1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [h1497, h1598, hc34, hlam, hphi, ht0b, ht45, ht5b, p1605_1, u0elo1]
                                · have p1605_0 := h1605c.1
                                  have p1605_1 := h1605c.2.1
                                  have p1605_2 := h1605c.2.2.1
                                  have p1605_3 := h1605c.2.2.2
                                  linarith only [hlam, p1605_0]
                        · linarith only [h1498, h1499, h1598, hc23, hc35, hlam, hphi]
                    · linarith only [h1498, h1499, h1595, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h1497, h1594, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1496, h1593, hlam]
              · linarith only [h0, h1495, h1592, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1648 | h1648
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1649 | h1649
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1650 | h1650
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1651 | h1651
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1652 | h1652
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1653 | h1653
                    · linarith only [h1494, h1498, h1648, h1653, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1655 | h1655
                      · linarith only [h1494, h1655, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · linarith only [h1498, h1648, h1650, h1655, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1494, h1497, h1650, h1652, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h1494, h1496, h1648, h1651, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
              · linarith only [h0, h1494, h1648, h1650, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h1498, h1648, h1649, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1662 | h1662
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1663 | h1663
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1664 | h1664
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1665 | h1665
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1666 | h1666
                    · linarith only [h1494, h1498, h1666, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1668 | h1668
                      · linarith only [h0, h1494, h1648, h1668, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1670 | h1670
                        · linarith only [h1495, h1498, h1670, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1672 | h1672
                          · linarith only [h1494, h1648, h1663, h1672, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1674 | h1674
                            · linarith only [h1496, h1674, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1676 | h1676
                              · rcases h2bigk with h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c | h1677c
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h0, hlam, p1677_1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  rcases p1677_3 (m.d 0 2) (by simp) with h1680 | h1680
                                  · rcases p1677_3 (m.d 1 2) (by simp) with h1681 | h1681
                                    · rcases p1677_3 (m.d 2 3) (by simp) with h1682 | h1682
                                      · linarith only [h1682, hlam, p1677_0]
                                      · rcases p1677_3 (m.d 2 4) (by simp) with h1684 | h1684
                                        · linarith only [h1496, h1684, hlam]
                                        · linarith only [h1670, h1684, hlam]
                                    · linarith only [h1663, h1681, hlam]
                                  · linarith only [h1680, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  rcases p1677_3 (m.d 0 2) (by simp) with h1689 | h1689
                                  · rcases p1677_3 (m.d 1 2) (by simp) with h1690 | h1690
                                    · rcases p1677_3 (m.d 2 3) (by simp) with h1691 | h1691
                                      · linarith only [h1495, h1691, hlam]
                                      · rcases p1677_3 (m.d 2 4) (by simp) with h1693 | h1693
                                        · linarith only [h1693, hlam, p1677_0]
                                        · rcases p1677_3 (m.d 2 5) (by simp) with h1695 | h1695
                                          · linarith only [h1497, h1695, hlam]
                                          · linarith only [h1674, h1695, hlam]
                                    · linarith only [h1664, h1690, hlam]
                                  · linarith only [h1689, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1677_1, u0elo1, u5ehi2]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1496, h1662, h1674, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1677_1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  rcases p1677_3 (m.d 0 2) (by simp) with h1703 | h1703
                                  · linarith only [h0, h1703, hlam]
                                  · linarith only [h1495, h1703, hlam]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  rcases p1677_3 (m.d 0 2) (by simp) with h1706 | h1706
                                  · linarith only [h0, h1706, hlam]
                                  · linarith only [h1496, h1706, hlam]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  rcases p1677_3 (m.d 0 2) (by simp) with h1709 | h1709
                                  · linarith only [h0, h1709, hlam]
                                  · linarith only [h1497, h1709, hlam]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1495, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1663, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1670, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1672, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1496, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1664, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1496, h1662, h1674, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1677_1, u0elo1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1674, hlam, p1677_1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1497, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1665, hlam, p1677_0]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1677_1, u0elo1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [h1496, h1662, h1674, hc24, hlam, hphi, ht0b, ht45, ht5b, p1677_1, u0elo1]
                                · have p1677_0 := h1677c.1
                                  have p1677_1 := h1677c.2.1
                                  have p1677_2 := h1677c.2.2.1
                                  have p1677_3 := h1677c.2.2.2
                                  linarith only [hlam, p1677_0]
                              · linarith only [h1498, h1662, h1676, hlam]
                  · linarith only [h0, h1497, h1665, hlam]
                · linarith only [h0, h1496, h1664, hlam]
              · linarith only [h0, h1495, h1663, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1731 | h1731
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1732 | h1732
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1733 | h1733
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1734 | h1734
                    · linarith only [h1494, h1498, h1734, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1736 | h1736
                      · linarith only [h1494, h1648, h1736, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1738 | h1738
                        · linarith only [h1494, h1498, h1731, h1738, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1740 | h1740
                          · linarith only [h1494, h1648, h1731, h1740, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1742 | h1742
                            · linarith only [h1496, h1662, h1742, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1744 | h1744
                              · rcases h2bigk with h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c | h1745c
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h0, hlam, p1745_1]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  rcases p1745_3 (m.d 0 2) (by simp) with h1748 | h1748
                                  · rcases p1745_3 (m.d 1 2) (by simp) with h1749 | h1749
                                    · rcases p1745_3 (m.d 2 3) (by simp) with h1750 | h1750
                                      · linarith only [h1750, hlam, p1745_0]
                                      · rcases p1745_3 (m.d 2 4) (by simp) with h1752 | h1752
                                        · linarith only [h1496, h1752, hlam]
                                        · linarith only [h1738, h1752, hlam]
                                    · linarith only [h1731, h1749, hlam]
                                  · linarith only [h1748, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  rcases p1745_3 (m.d 0 2) (by simp) with h1757 | h1757
                                  · rcases p1745_3 (m.d 1 2) (by simp) with h1758 | h1758
                                    · rcases p1745_3 (m.d 2 3) (by simp) with h1759 | h1759
                                      · linarith only [h1495, h1759, hlam]
                                      · rcases p1745_3 (m.d 2 4) (by simp) with h1761 | h1761
                                        · linarith only [h1761, hlam, p1745_0]
                                        · rcases p1745_3 (m.d 2 5) (by simp) with h1763 | h1763
                                          · linarith only [h1497, h1763, hlam]
                                          · linarith only [h1742, h1763, hlam]
                                    · linarith only [h1732, h1758, hlam]
                                  · linarith only [h1757, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1745_1, u0elo1, u5ehi2]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1497, hc12, hlam, hphi, ht01, ht0b, ht5b, p1745_1, u5ehi2]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  rcases p1745_3 (m.d 0 2) (by simp) with h1771 | h1771
                                  · linarith only [h0, h1771, hlam]
                                  · linarith only [h1495, h1771, hlam]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  rcases p1745_3 (m.d 0 2) (by simp) with h1774 | h1774
                                  · linarith only [h0, h1774, hlam]
                                  · linarith only [h1496, h1774, hlam]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  rcases p1745_3 (m.d 0 2) (by simp) with h1777 | h1777
                                  · linarith only [h0, h1777, hlam]
                                  · linarith only [h1497, h1777, hlam]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1495, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1731, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1738, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1740, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1496, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1732, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1745_1, u0elo1]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1742, hlam, p1745_1]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1497, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1733, hlam, p1745_0]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1745_1, u0elo1]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [h1497, hc24, hlam, hphi, ht0b, ht45, ht5b, p1745_1, u0elo1]
                                · have p1745_0 := h1745c.1
                                  have p1745_1 := h1745c.2.1
                                  have p1745_2 := h1745c.2.2.1
                                  have p1745_3 := h1745c.2.2.2
                                  linarith only [hlam, p1745_0]
                              · rcases h2bigk with h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c | h1795c
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h0, hlam, p1795_1]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  rcases p1795_3 (m.d 0 2) (by simp) with h1798 | h1798
                                  · rcases p1795_3 (m.d 1 2) (by simp) with h1799 | h1799
                                    · rcases p1795_3 (m.d 2 3) (by simp) with h1800 | h1800
                                      · linarith only [h1800, hlam, p1795_0]
                                      · rcases p1795_3 (m.d 2 4) (by simp) with h1802 | h1802
                                        · linarith only [h1496, h1802, hlam]
                                        · linarith only [h1738, h1802, hlam]
                                    · linarith only [h1731, h1799, hlam]
                                  · linarith only [h1798, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  rcases p1795_3 (m.d 0 2) (by simp) with h1807 | h1807
                                  · rcases p1795_3 (m.d 1 2) (by simp) with h1808 | h1808
                                    · rcases p1795_3 (m.d 2 3) (by simp) with h1809 | h1809
                                      · linarith only [h1495, h1809, hlam]
                                      · rcases p1795_3 (m.d 2 4) (by simp) with h1811 | h1811
                                        · linarith only [h1811, hlam, p1795_0]
                                        · rcases p1795_3 (m.d 2 5) (by simp) with h1813 | h1813
                                          · linarith only [h1497, h1813, hlam]
                                          · linarith only [h1742, h1813, hlam]
                                    · linarith only [h1732, h1808, hlam]
                                  · linarith only [h1807, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, hphi, ht0b, ht5b, p1795_1, u0elo1, u5ehi2]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1497, hc12, hlam, hphi, ht01, ht0b, ht5b, p1795_1, u5ehi2]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  rcases p1795_3 (m.d 0 2) (by simp) with h1821 | h1821
                                  · linarith only [h0, h1821, hlam]
                                  · linarith only [h1495, h1821, hlam]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  rcases p1795_3 (m.d 0 2) (by simp) with h1824 | h1824
                                  · linarith only [h0, h1824, hlam]
                                  · linarith only [h1496, h1824, hlam]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  rcases p1795_3 (m.d 0 2) (by simp) with h1827 | h1827
                                  · linarith only [h0, h1827, hlam]
                                  · linarith only [h1497, h1827, hlam]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1495, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1731, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1738, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1740, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1496, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1732, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1795_1, u0elo1]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1742, hlam, p1795_1]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1497, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1733, hlam, p1795_0]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1497, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1795_1, u0elo1]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [h1497, hc24, hlam, hphi, ht0b, ht45, ht5b, p1795_1, u0elo1]
                                · have p1795_0 := h1795c.1
                                  have p1795_1 := h1795c.2.1
                                  have p1795_2 := h1795c.2.2.1
                                  have p1795_3 := h1795c.2.2.2
                                  linarith only [hlam, p1795_0]
                  · linarith only [h0, h1494, h1497, h1731, h1733, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h1496, h1732, hlam]
              · linarith only [h0, h1494, h1495, h1731, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1848 | h1848
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1849 | h1849
          · linarith only [h0, h1494, h1497, h1849, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1851 | h1851
            · linarith only [h0, h1494, h1497, h1848, h1851, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1853 | h1853
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1854 | h1854
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1855 | h1855
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1856 | h1856
                    · linarith only [h0, h1494, h1497, h1855, h1856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1494, h1497, h1848, h1855, h1856, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1859 | h1859
                    · linarith only [h0, h1494, h1855, h1859, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1848, h1849, h1859, hc13, hc35, hlam, hphi]
                · linarith only [h0, h1496, h1854, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1495, h1853, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1864 | h1864
          · linarith only [h0, h1494, h1497, h1864, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1866 | h1866
            · linarith only [h1496, h1497, h1866, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1868 | h1868
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1869 | h1869
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1870 | h1870
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1871 | h1871
                    · linarith only [h0, h1494, h1497, h1848, h1870, h1871, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1873 | h1873
                      · linarith only [h0, h1494, h1497, h1864, h1873, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1875 | h1875
                        · linarith only [h1494, h1848, h1868, h1875, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1877 | h1877
                          · linarith only [h0, h1494, h1497, h1868, h1870, h1873, h1877, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1879 | h1879
                            · linarith only [h1496, h1497, h1866, h1870, h1879, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1881 | h1881
                              · linarith only [h0, h1494, h1497, h1868, h1879, h1881, hc23, hc34, hlam, hphi]
                              · rcases h2bigk with h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c | h1883c
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h0, hlam, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1497, h1870, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1497, h1870, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1497, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  rcases p1883_3 (m.d 0 2) (by simp) with h1889 | h1889
                                  · linarith only [h0, h1889, hlam]
                                  · rcases p1883_3 (m.d 1 2) (by simp) with h1891 | h1891
                                    · rcases p1883_3 (m.d 2 3) (by simp) with h1892 | h1892
                                      · linarith only [h1868, h1892, hlam]
                                      · rcases p1883_3 (m.d 2 4) (by simp) with h1894 | h1894
                                        · linarith only [h1869, h1894, hlam]
                                        · rcases p1883_3 (m.d 2 5) (by simp) with h1896 | h1896
                                          · linarith only [h1870, h1896, hlam]
                                          · linarith only [h1497, h1896, hlam]
                                    · linarith only [h0, h1891, hlam]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1495, h1497, h1870, hlam, p1883_2]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1496, h1497, h1870, hlam, p1883_2]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h0, h1497, hc01, hc12, hlam, hphi, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1495, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1868, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1875, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1877, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1496, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1869, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1496, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1883_1, u0elo1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1879, hlam, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h0, h1494, h1868, h1870, h1873, hc23, hc35, hlam, hphi, p1883_1]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [h1870, hlam, p1883_0]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  rcases p1883_3 (m.d 0 2) (by simp) with h1916 | h1916
                                  · linarith only [h1497, h1916, hlam]
                                  · linarith only [h1495, h1916, hlam]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  rcases p1883_3 (m.d 0 2) (by simp) with h1919 | h1919
                                  · linarith only [h1497, h1919, hlam]
                                  · linarith only [h1496, h1919, hlam]
                                · have p1883_0 := h1883c.1
                                  have p1883_1 := h1883c.2.1
                                  have p1883_2 := h1883c.2.2.1
                                  have p1883_3 := h1883c.2.2.2
                                  linarith only [hlam, p1883_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1923 | h1923
                    · linarith only [h0, h1494, h1870, h1923, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1925 | h1925
                      · linarith only [h0, h1494, h1870, h1925, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1927 | h1927
                        · linarith only [h1494, h1848, h1868, h1927, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1929 | h1929
                          · linarith only [h0, h1494, h1864, h1868, h1870, h1929, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                          · linarith only [h0, h1494, h1868, h1870, h1929, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1494, h1496, h1868, h1869, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1495, h1868, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1934 | h1934
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1935 | h1935
        · linarith only [h0, h1494, h1496, h1935, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1937 | h1937
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1938 | h1938
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1939 | h1939
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1940 | h1940
                · linarith only [h1496, h1934, h1940, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · linarith only [h0, h1494, h1937, h1940, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · linarith only [h0, h1494, h1937, h1939, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h1496, h1934, h1938, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1945 | h1945
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1946 | h1946
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1947 | h1947
                · linarith only [h1496, h1934, h1947, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1949 | h1949
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1950 | h1950
                    · linarith only [h0, h1494, h1947, h1950, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1952 | h1952
                      · linarith only [h0, h1494, h1937, h1947, h1952, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1954 | h1954
                        · linarith only [h0, h1494, h1934, h1946, h1947, h1950, h1954, hlam, hphi, ht0b, ht5b, u0elo2, u5ehi2]
                        · linarith only [h0, h1494, h1946, h1947, h1954, hc23, hc34, hlam, hphi]
                  · linarith only [h0, h1494, h1934, h1946, h1949, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
              · linarith only [h0, h1495, h1946, hlam]
            · linarith only [h1496, h1934, h1945, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1960 | h1960
        · linarith only [h0, h1494, h1496, h1960, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1962 | h1962
          · linarith only [h0, h1494, h1934, h1962, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1964 | h1964
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1965 | h1965
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1966 | h1966
                · rcases m.htr 1 2 5 (by decide) (by decide) with h1967 | h1967
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h1968 | h1968
                    · linarith only [h1494, h1960, h1968, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1970 | h1970
                      · linarith only [h0, h1494, h1496, h1962, h1966, h1970, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1972 | h1972
                        · linarith only [h1495, h1496, h1966, h1968, h1972, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1974 | h1974
                          · linarith only [h0, h1494, h1934, h1965, h1967, h1970, h1974, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1976 | h1976
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1977 | h1977
                              · rcases h2bigk with h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c | h1978c
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, hlam, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1934, h1966, h1976, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1496, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1934, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  rcases p1978_3 (m.d 0 2) (by simp) with h1984 | h1984
                                  · linarith only [h0, h1984, hlam]
                                  · rcases p1978_3 (m.d 1 2) (by simp) with h1986 | h1986
                                    · rcases p1978_3 (m.d 2 3) (by simp) with h1987 | h1987
                                      · linarith only [h1965, h1987, hlam]
                                      · rcases p1978_3 (m.d 2 4) (by simp) with h1989 | h1989
                                        · linarith only [h1966, h1989, hlam]
                                        · linarith only [h1496, h1989, hlam]
                                    · linarith only [h0, h1986, hlam]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1495, h1934, h1966, h1976, hlam, p1978_2]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, h1934, h1976, hc01, hc12, hlam, hphi, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, h1494, h1934, h1965, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1495, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1965, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1972, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1974, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, h1494, h1965, h1966, h1968, hc23, hc34, hlam, hphi, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1966, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  rcases p1978_3 (m.d 0 2) (by simp) with h2004 | h2004
                                  · linarith only [h1496, h2004, hlam]
                                  · linarith only [h1495, h2004, hlam]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, h1494, h1934, h1965, h1966, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h0, h1494, h1965, h1967, h1970, hc23, hc35, hlam, hphi, p1978_1]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1967, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  rcases p1978_3 (m.d 0 2) (by simp) with h2011 | h2011
                                  · linarith only [h1934, h2011, hlam]
                                  · linarith only [h1495, h2011, hlam]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [h1976, hlam, p1978_0]
                                · have p1978_0 := h1978c.1
                                  have p1978_1 := h1978c.2.1
                                  have p1978_2 := h1978c.2.2.1
                                  have p1978_3 := h1978c.2.2.2
                                  linarith only [hlam, p1978_0]
                              · linarith only [h1960, h1964, h1977, hlam]
                            · linarith only [h0, h1494, h1496, h1964, h1965, h1976, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1494, h1496, h1965, h1966, h1967, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2019 | h2019
                  · linarith only [h0, h1494, h1934, h1965, h1966, h2019, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2021 | h2021
                    · linarith only [h0, h1494, h1960, h1966, h2021, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2023 | h2023
                      · linarith only [h0, h1494, h1966, h2023, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2025 | h2025
                        · linarith only [h0, h1494, h1965, h1966, h2021, h2025, hlam]
                        · linarith only [h0, h1494, h1966, h2025, hc13, hc34, hlam, hphi]
              · linarith only [h0, h1494, h1495, h1965, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h2029 | h2029
              · rcases m.htr 1 2 4 (by decide) (by decide) with h2030 | h2030
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2031 | h2031
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2032 | h2032
                    · linarith only [h0, h1494, h1496, h2030, h2032, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2034 | h2034
                      · linarith only [h0, h1494, h1496, h2030, h2034, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2036 | h2036
                        · linarith only [h0, h1494, h1496, h2029, h2030, h2032, h2036, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2038 | h2038
                          · linarith only [h0, h1494, h1496, h2029, h2030, h2034, h2038, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2040 | h2040
                            · linarith only [h0, h1496, h1964, h2030, h2040, hc01, hc12, hlam, hphi]
                            · linarith only [h0, h1494, h1496, h2029, h2040, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1494, h1496, h2029, h2030, h2031, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h2044 | h2044
                  · linarith only [h0, h1494, h1934, h2029, h2030, h2044, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h2046 | h2046
                    · linarith only [h0, h1494, h2030, h2046, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h2048 | h2048
                      · linarith only [h1494, h2048, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2050 | h2050
                        · linarith only [h0, h1494, h2029, h2030, h2046, h2050, hlam]
                        · linarith only [h0, h1494, h2030, h2050, hc13, hc34, hlam, hphi]
              · linarith only [h0, h1494, h1495, h2029, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
  · linarith only [h0, h1494, h1495, hlam]

end R2N4
