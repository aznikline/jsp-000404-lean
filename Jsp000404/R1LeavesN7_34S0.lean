import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5716000 in
theorem r1l7_10_12_23_L_I_L_R_H_I_s1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg1265 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1561 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1265 := hg1265
  rcases m.htr 0 2 3 (by decide) (by decide) with h1562 | h1562
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1563 | h1563
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1564 | h1564
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1565 | h1565
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1566 | h1566
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1567 | h1567
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1568 | h1568
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1569 | h1569
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1570 | h1570
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1571 | h1571
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1572 | h1572
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1573 | h1573
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1574 | h1574
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1575 | h1575
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1576 | h1576
                              · rcases h0bigk with h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c | h1577c
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h0, hlam, p1577_1]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1265, hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1265, h1563, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1577_1, u2ehi3]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1265, h1564, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1577_1, u2ehi4]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1583 | h1583
                                  · linarith only [h0, h1583, hlam]
                                  · rcases p1577_3 (m.d 0 2) (by simp) with h1585 | h1585
                                    · rcases p1577_3 (m.d 0 3) (by simp) with h1586 | h1586
                                      · linarith only [h1562, h1586, hlam]
                                      · linarith only [h1265, h1586, hlam]
                                    · linarith only [h0, h1585, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h0, h1565, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1577_1]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1592 | h1592
                                  · linarith only [h0, h1592, hlam]
                                  · rcases p1577_3 (m.d 0 2) (by simp) with h1594 | h1594
                                    · rcases p1577_3 (m.d 0 3) (by simp) with h1595 | h1595
                                      · linarith only [h1562, h1595, hlam]
                                      · linarith only [h1565, h1595, hlam]
                                    · linarith only [h1563, h1594, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1599 | h1599
                                  · linarith only [h0, h1599, hlam]
                                  · linarith only [h1561, h1599, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1602 | h1602
                                  · linarith only [h1265, h1602, hlam]
                                  · rcases p1577_3 (m.d 0 2) (by simp) with h1604 | h1604
                                    · rcases p1577_3 (m.d 0 3) (by simp) with h1605 | h1605
                                      · rcases p1577_3 (m.d 0 4) (by simp) with h1606 | h1606
                                        · linarith only [h1565, h1606, hlam]
                                        · rcases p1577_3 (m.d 0 5) (by simp) with h1608 | h1608
                                          · linarith only [h1566, h1608, hlam]
                                          · rcases h3bigk with h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c | h1610c
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1265, hlam, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1265, h1568, h1573, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1265, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              rcases p1610_3 (m.d 0 3) (by simp) with h1615 | h1615
                                              · rcases p1610_3 (m.d 1 3) (by simp) with h1616 | h1616
                                                · rcases p1610_3 (m.d 2 3) (by simp) with h1617 | h1617
                                                  · linarith only [h1562, h1617, hlam]
                                                  · linarith only [h1574, h1617, hlam]
                                                · linarith only [h1571, h1616, hlam]
                                              · linarith only [h1615, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1568, hc01, hc12, hlam, hphi, p1577_1, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1568, h1573, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              rcases p1610_3 (m.d 0 3) (by simp) with h1626 | h1626
                                              · linarith only [h1265, h1626, hlam]
                                              · linarith only [h1566, h1626, hlam]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1562, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1568, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1576, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h0, h1562, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1565, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1570, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1573, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1265, h1565, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1610_1]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1566, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1571, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1574, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [h1576, hlam, p1610_0]
                                            · have p1610_0 := h1610c.1
                                              have p1610_1 := h1610c.2.1
                                              have p1610_2 := h1610c.2.2.1
                                              have p1610_3 := h1610c.2.2.2
                                              linarith only [hlam, p1610_0]
                                      · linarith only [h1265, h1605, hlam]
                                    · linarith only [h0, h1604, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1562, hlam, p1577_1]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1648 | h1648
                                  · linarith only [h1265, h1648, hlam]
                                  · rcases p1577_3 (m.d 0 2) (by simp) with h1650 | h1650
                                    · rcases p1577_3 (m.d 0 3) (by simp) with h1651 | h1651
                                      · rcases p1577_3 (m.d 0 4) (by simp) with h1652 | h1652
                                        · linarith only [h1565, h1652, hlam]
                                        · rcases p1577_3 (m.d 0 5) (by simp) with h1654 | h1654
                                          · linarith only [h1566, h1654, hlam]
                                          · rcases h3bigk with h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c | h1656c
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1265, hlam, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1265, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1656_1, u2ehi2]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1265, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              rcases p1656_3 (m.d 0 3) (by simp) with h1661 | h1661
                                              · rcases p1656_3 (m.d 1 3) (by simp) with h1662 | h1662
                                                · rcases p1656_3 (m.d 2 3) (by simp) with h1663 | h1663
                                                  · linarith only [h1562, h1663, hlam]
                                                  · linarith only [h1574, h1663, hlam]
                                                · linarith only [h1571, h1662, hlam]
                                              · linarith only [h1661, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1568, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1577_1, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1568, h1573, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              rcases p1656_3 (m.d 0 3) (by simp) with h1672 | h1672
                                              · linarith only [h1265, h1672, hlam]
                                              · linarith only [h1566, h1672, hlam]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1562, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1568, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1576, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h0, h1562, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1565, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1570, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1573, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1265, h1565, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1656_1]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1566, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1571, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1574, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [h1576, hlam, p1656_0]
                                            · have p1656_0 := h1656c.1
                                              have p1656_1 := h1656c.2.1
                                              have p1656_2 := h1656c.2.2.1
                                              have p1656_3 := h1656c.2.2.2
                                              linarith only [hlam, p1656_0]
                                      · linarith only [h1565, h1651, hlam]
                                    · linarith only [h1563, h1650, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1692 | h1692
                                  · linarith only [h1265, h1692, hlam]
                                  · linarith only [h1561, h1692, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1695 | h1695
                                  · linarith only [h1695, hlam, p1577_0]
                                  · rcases p1577_3 (m.d 0 2) (by simp) with h1697 | h1697
                                    · rcases p1577_3 (m.d 0 3) (by simp) with h1698 | h1698
                                      · rcases p1577_3 (m.d 0 4) (by simp) with h1699 | h1699
                                        · rcases p1577_3 (m.d 0 5) (by simp) with h1700 | h1700
                                          · linarith only [h1567, h1700, hlam]
                                          · rcases h3bigk with h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1265, hlam, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1265, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1702_1, u2ehi2]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1265, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              rcases p1702_3 (m.d 0 3) (by simp) with h1707 | h1707
                                              · rcases p1702_3 (m.d 1 3) (by simp) with h1708 | h1708
                                                · rcases p1702_3 (m.d 2 3) (by simp) with h1709 | h1709
                                                  · linarith only [h1562, h1709, hlam]
                                                  · linarith only [h1574, h1709, hlam]
                                                · linarith only [h1571, h1708, hlam]
                                              · linarith only [h1707, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1265, h1561, h1564, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1702_1, u2ehi4]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1568, h1573, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              rcases p1702_3 (m.d 0 3) (by simp) with h1718 | h1718
                                              · linarith only [h1265, h1718, hlam]
                                              · linarith only [h1566, h1718, hlam]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1562, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1568, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1576, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h0, h1562, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1565, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1570, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1573, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1265, h1565, h1568, h1576, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1702_1]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1566, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1571, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1574, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [h1576, hlam, p1702_0]
                                            · have p1702_0 := h1702c.1
                                              have p1702_1 := h1702c.2.1
                                              have p1702_2 := h1702c.2.2.1
                                              have p1702_3 := h1702c.2.2.2
                                              linarith only [hlam, p1702_0]
                                        · linarith only [h1699, hlam, p1577_0]
                                      · linarith only [h1265, h1698, hlam]
                                    · linarith only [h0, h1697, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1563, hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1565, hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  rcases p1577_3 (m.d 0 1) (by simp) with h1742 | h1742
                                  · linarith only [h1265, h1564, h1568, h1742, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1577_1, u2ehi4]
                                  · linarith only [h1561, h1742, hlam]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1561, hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1564, hlam, p1577_1]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1566, hlam, p1577_0]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [h1567, hlam, p1577_1]
                                · have p1577_0 := h1577c.1
                                  have p1577_1 := h1577c.2.1
                                  have p1577_2 := h1577c.2.2.1
                                  have p1577_3 := h1577c.2.2.2
                                  linarith only [hlam, p1577_0]
                              · rcases h0bigk with h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c | h1750c
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h0, hlam, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1265, hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1265, h1563, h1568, h1575, h1576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1265, h1564, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u2ehi4]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h0, h1561, h1572, h1576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h0, h1265, h1561, h1572, h1576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h0, h1563, h1575, h1576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  rcases p1750_3 (m.d 0 1) (by simp) with h1760 | h1760
                                  · linarith only [h0, h1760, hlam]
                                  · linarith only [h1561, h1760, hlam]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1561, h1572, h1576, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1562, hlam, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1265, h1563, h1568, h1575, h1576, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  rcases p1750_3 (m.d 0 1) (by simp) with h1767 | h1767
                                  · linarith only [h1265, h1767, hlam]
                                  · linarith only [h1561, h1767, hlam]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1561, h1572, h1576, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1563, hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1565, hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  rcases p1750_3 (m.d 0 1) (by simp) with h1774 | h1774
                                  · linarith only [h1265, h1564, h1568, h1774, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1750_1, u2ehi4]
                                  · linarith only [h1561, h1774, hlam]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1561, hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1564, hlam, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1566, hlam, p1750_0]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [h1567, hlam, p1750_1]
                                · have p1750_0 := h1750c.1
                                  have p1750_1 := h1750c.2.1
                                  have p1750_2 := h1750c.2.2.1
                                  have p1750_3 := h1750c.2.2.2
                                  linarith only [hlam, p1750_0]
                            · linarith only [h1265, h1561, h1568, h1572, h1575, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h1265, h1561, h1568, h1571, h1574, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1784 | h1784
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1785 | h1785
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1786 | h1786
                              · rcases h0bigk with h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c | h1787c
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h0, hlam, p1787_1]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1265, hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1265, h1563, h1568, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1265, h1564, h1568, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1793 | h1793
                                  · linarith only [h0, h1793, hlam]
                                  · rcases p1787_3 (m.d 0 2) (by simp) with h1795 | h1795
                                    · rcases p1787_3 (m.d 0 3) (by simp) with h1796 | h1796
                                      · linarith only [h1562, h1796, hlam]
                                      · linarith only [h1265, h1796, hlam]
                                    · linarith only [h0, h1795, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h0, h1565, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h0, h1565, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1803 | h1803
                                  · linarith only [h0, h1803, hlam]
                                  · linarith only [h1561, h1803, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1806 | h1806
                                  · linarith only [h1265, h1806, hlam]
                                  · rcases p1787_3 (m.d 0 2) (by simp) with h1808 | h1808
                                    · rcases p1787_3 (m.d 0 3) (by simp) with h1809 | h1809
                                      · rcases p1787_3 (m.d 0 4) (by simp) with h1810 | h1810
                                        · linarith only [h1565, h1810, hlam]
                                        · linarith only [h1565, h1573, h1784, h1810, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                      · linarith only [h1265, h1809, hlam]
                                    · linarith only [h0, h1808, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1562, hlam, p1787_1]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1265, h1565, h1568, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1818 | h1818
                                  · linarith only [h1265, h1818, hlam]
                                  · linarith only [h1561, h1818, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1821 | h1821
                                  · linarith only [h1821, hlam, p1787_0]
                                  · rcases p1787_3 (m.d 0 2) (by simp) with h1823 | h1823
                                    · rcases p1787_3 (m.d 0 3) (by simp) with h1824 | h1824
                                      · rcases p1787_3 (m.d 0 4) (by simp) with h1825 | h1825
                                        · rcases p1787_3 (m.d 0 5) (by simp) with h1826 | h1826
                                          · linarith only [h1567, h1826, hlam]
                                          · rcases h3bigk with h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c | h1828c
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1265, hlam, p1828_1]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1265, h1568, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1828_1, u2ehi4]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1265, h1568, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1828_1, u2ehi4]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              rcases p1828_3 (m.d 0 3) (by simp) with h1833 | h1833
                                              · rcases p1828_3 (m.d 1 3) (by simp) with h1834 | h1834
                                                · rcases p1828_3 (m.d 2 3) (by simp) with h1835 | h1835
                                                  · linarith only [h1562, h1835, hlam]
                                                  · linarith only [h1784, h1835, hlam]
                                                · linarith only [h1571, h1834, hlam]
                                              · linarith only [h1833, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1265, h1568, hc01, hc12, hlam, hphi, p1828_1]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1568, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1828_1, u2ehi4]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1568, h1573, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1828_1, u2ehi4]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              rcases p1828_3 (m.d 0 3) (by simp) with h1844 | h1844
                                              · linarith only [h1265, h1844, hlam]
                                              · linarith only [h1566, h1844, hlam]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1562, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1568, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1573, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1573, h1786, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1828_1]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1565, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1570, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hc23, hc34, hlam, hphi, p1828_1]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1265, h1565, h1568, h1786, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1828_1]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1566, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1571, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1784, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [h1786, hlam, p1828_0]
                                            · have p1828_0 := h1828c.1
                                              have p1828_1 := h1828c.2.1
                                              have p1828_2 := h1828c.2.2.1
                                              have p1828_3 := h1828c.2.2.2
                                              linarith only [hlam, p1828_0]
                                        · linarith only [h1825, hlam, p1787_0]
                                      · linarith only [h1265, h1824, hlam]
                                    · linarith only [h0, h1823, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1563, hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1565, hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  rcases p1787_3 (m.d 0 1) (by simp) with h1868 | h1868
                                  · linarith only [h1265, h1564, h1568, h1868, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1787_1, u2ehi4]
                                  · linarith only [h1561, h1868, hlam]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1561, hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1564, hlam, p1787_1]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1566, hlam, p1787_0]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [h1567, hlam, p1787_1]
                                · have p1787_0 := h1787c.1
                                  have p1787_1 := h1787c.2.1
                                  have p1787_2 := h1787c.2.2.1
                                  have p1787_3 := h1787c.2.2.2
                                  linarith only [hlam, p1787_0]
                              · linarith only [h1265, h1561, h1568, h1572, h1573, h1784, h1786, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · linarith only [h1265, h1561, h1568, h1572, h1573, h1784, h1785, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                          · linarith only [h1265, h1561, h1568, h1571, h1784, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1879 | h1879
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1880 | h1880
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1881 | h1881
                            · linarith only [h1569, h1572, h1881, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1883 | h1883
                              · linarith only [h1569, h1572, h1879, h1883, hc23, hlam, hphi, u2ehi3]
                              · rcases h0bigk with h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c | h1885c
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h0, hlam, p1885_1]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, h1567, h1568, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, h1567, h1568, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h0, h1561, h1567, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h0, h1265, h1561, h1567, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h0, h1567, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h0, h1567, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1561, h1567, h1569, h1572, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1562, hlam, p1885_1]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, h1567, h1568, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, h1567, h1568, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1561, h1567, h1569, h1572, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1563, hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1565, hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1265, h1565, h1567, h1568, h1569, h1572, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1885_1, u2ehi3]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1561, hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1564, hlam, p1885_1]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1566, hlam, p1885_0]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [h1567, hlam, p1885_1]
                                · have p1885_0 := h1885c.1
                                  have p1885_1 := h1885c.2.1
                                  have p1885_2 := h1885c.2.2.1
                                  have p1885_3 := h1885c.2.2.2
                                  linarith only [hlam, p1885_0]
                          · linarith only [h0, h1561, h1571, h1880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1570, h1572, h1879, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1265, h1561, h1564, h1571, hc35, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1265, h1565, h1570, hlam]
                · linarith only [h0, h1561, h1564, h1569, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1563, h1568, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1917 | h1917
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1918 | h1918
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1919 | h1919
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1920 | h1920
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1921 | h1921
                      · linarith only [h1265, h1561, h1563, h1567, h1917, h1921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1923 | h1923
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1924 | h1924
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1925 | h1925
                            · linarith only [h1563, h1567, h1925, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1927 | h1927
                              · linarith only [h1562, h1921, h1923, h1927, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c | h1929c
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h0, hlam, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1265, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1265, h1563, h1917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1265, h1564, h1917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi4]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h0, h1561, h1918, h1921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h0, h1265, h1561, h1918, h1921, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  rcases p1929_3 (m.d 0 1) (by simp) with h1938 | h1938
                                  · linarith only [h0, h1938, hlam]
                                  · linarith only [h1561, h1567, h1918, h1921, h1938, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  rcases p1929_3 (m.d 0 1) (by simp) with h1941 | h1941
                                  · linarith only [h0, h1941, hlam]
                                  · linarith only [h1561, h1941, hlam]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1561, h1918, h1921, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1562, hlam, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  rcases p1929_3 (m.d 0 1) (by simp) with h1947 | h1947
                                  · linarith only [h1265, h1947, hlam]
                                  · linarith only [h1561, h1567, h1947, hlam]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  rcases p1929_3 (m.d 0 1) (by simp) with h1950 | h1950
                                  · linarith only [h1265, h1950, hlam]
                                  · linarith only [h1561, h1950, hlam]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1561, h1918, h1921, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1563, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1565, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1567, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1561, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1564, hlam, p1929_1]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1566, hlam, p1929_0]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [h1265, h1561, h1563, h1917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1929_1, u2ehi3]
                                · have p1929_0 := h1929c.1
                                  have p1929_1 := h1929c.2.1
                                  have p1929_2 := h1929c.2.2.1
                                  have p1929_3 := h1929c.2.2.2
                                  linarith only [hlam, p1929_0]
                          · linarith only [h1265, h1561, h1917, h1920, h1924, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1565, h1567, h1923, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h1265, h1561, h1564, h1920, hc35, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h1265, h1561, h1564, h1919, hc34, hlam, hphi, ht23, u2ehi4]
                · linarith only [h1265, h1561, h1563, h1567, h1917, h1918, hlam]
              · linarith only [h0, h1561, h1563, h1567, h1917, hc23, hlam, hphi, u2ehi3]
          · linarith only [h1265, h1561, h1566, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1970 | h1970
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1971 | h1971
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1972 | h1972
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1973 | h1973
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1974 | h1974
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1975 | h1975
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1976 | h1976
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1977 | h1977
                        · linarith only [h1265, h1561, h1562, h1564, h1565, h1977, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1979 | h1979
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1980 | h1980
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1981 | h1981
                              · rcases h0bigk with h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c | h1982c
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h0, hlam, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1265, hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1265, h1565, h1974, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1265, h1565, h1974, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  rcases p1982_3 (m.d 0 1) (by simp) with h1988 | h1988
                                  · linarith only [h0, h1988, hlam]
                                  · rcases p1982_3 (m.d 0 2) (by simp) with h1990 | h1990
                                    · rcases p1982_3 (m.d 0 3) (by simp) with h1991 | h1991
                                      · linarith only [h1562, h1991, hlam]
                                      · linarith only [h1265, h1991, hlam]
                                    · linarith only [h0, h1990, hlam]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  rcases p1982_3 (m.d 0 1) (by simp) with h1996 | h1996
                                  · linarith only [h0, h1996, hlam]
                                  · rcases p1982_3 (m.d 0 2) (by simp) with h1998 | h1998
                                    · rcases p1982_3 (m.d 0 3) (by simp) with h1999 | h1999
                                      · linarith only [h1562, h1999, hlam]
                                      · rcases p1982_3 (m.d 0 4) (by simp) with h2001 | h2001
                                        · linarith only [h1563, h2001, hlam]
                                        · linarith only [h1565, h2001, hlam]
                                    · linarith only [h1562, h1998, hlam]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  rcases p1982_3 (m.d 0 1) (by simp) with h2005 | h2005
                                  · linarith only [h0, h2005, hlam]
                                  · rcases p1982_3 (m.d 0 2) (by simp) with h2007 | h2007
                                    · rcases p1982_3 (m.d 0 3) (by simp) with h2008 | h2008
                                      · linarith only [h1562, h2008, hlam]
                                      · rcases p1982_3 (m.d 0 4) (by simp) with h2010 | h2010
                                        · linarith only [h1563, h2010, hlam]
                                        · rcases p1982_3 (m.d 0 5) (by simp) with h2012 | h2012
                                          · linarith only [h1564, h2012, hlam]
                                          · rcases h3bigk with h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c | h2014c
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1265, hlam, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h0, h1565, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, p2014_1, u2ehi4]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1565, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h0, h1565, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p1982_1, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1265, h1972, hc01, hc12, hlam, hphi, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1972, h1979, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2014_1, u2ehi4]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1265, h1561, h1564, h1565, h1972, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2014_1, u2ehi4]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              rcases p2014_3 (m.d 0 3) (by simp) with h2024 | h2024
                                              · linarith only [h1265, h2024, hlam]
                                              · linarith only [h1970, h2024, hlam]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1562, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1972, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1977, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h0, h1562, h1981, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1265, h1561, h1564, h1974, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2014_1, u2ehi4]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1974, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1972, h1974, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1972, h1974, h1981, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2014_1]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1970, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1975, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1979, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [h1981, hlam, p2014_0]
                                            · have p2014_0 := h2014c.1
                                              have p2014_1 := h2014c.2.1
                                              have p2014_2 := h2014c.2.2.1
                                              have p2014_3 := h2014c.2.2.2
                                              linarith only [hlam, p2014_0]
                                    · linarith only [h1563, h2007, hlam]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  rcases p1982_3 (m.d 0 1) (by simp) with h2043 | h2043
                                  · linarith only [h0, h2043, hlam]
                                  · linarith only [h1561, h2043, hlam]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1561, h1564, h1565, h1972, h1974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, u2ehi4]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1562, hlam, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1565, hlam, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1564, h1565, h1972, h1974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, u2ehi4]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1561, h1564, h1565, h1972, h1974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, u2ehi4]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1563, hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1265, h1561, h1564, h1565, h1972, h1974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, u2ehi4]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1564, h1565, h1972, h1974, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1982_1, u2ehi4]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1561, hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1564, hlam, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1970, hlam, p1982_0]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [h1971, hlam, p1982_1]
                                · have p1982_0 := h1982c.1
                                  have p1982_1 := h1982c.2.1
                                  have p1982_2 := h1982c.2.2.1
                                  have p1982_3 := h1982c.2.2.2
                                  linarith only [hlam, p1982_0]
                              · linarith only [h1265, h1561, h1564, h1565, h1981, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                            · linarith only [h1265, h1561, h1565, h1976, h1980, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h1265, h1561, h1565, h1972, h1974, h1975, h1979, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1265, h1561, h1565, h1971, h1972, h1973, h1974, h1976, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1265, h1565, h1974, h1975, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h1265, h1561, h1564, h1974, hc34, hlam, hphi, ht23, u2ehi4]
                · linarith only [h0, h1561, h1564, h1973, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h1561, h1562, h1564, h1972, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
            · linarith only [h1265, h1561, h1565, h1971, hlam]
          · linarith only [h1265, h1561, h1970, hlam]
      · linarith only [h1562, h1564, hc25, hlam, hphi, u2ehi2]
    · linarith only [h1562, h1563, hc24, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2073 | h2073
    · linarith only [h1562, h2073, hc23, hlam, hphi, u2ehi3]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2075 | h2075
      · linarith only [h1562, h2075, hc23, hlam, hphi, u2ehi4]
      · linarith only [h0, h1561, h2075, hlam]

end R2N4
