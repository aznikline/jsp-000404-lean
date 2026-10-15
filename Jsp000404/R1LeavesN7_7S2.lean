import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h939 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h941 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h1553 | h1553
  · linarith only [h0, h1553, h4, h7, h941, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1555 | h1555
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1556 | h1556
      · linarith only [h0, h1555, h1556, h4, h941, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1558 | h1558
        · linarith only [h1553, h1556, h1558, hc13, hc34, hlam, hphi]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1560 | h1560
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1561 | h1561
            · rcases h1bigk with h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c | h1562c
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h0, h10, h1558, h1561, h4, h7, hlam, p1562_2]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1565 | h1565
                · rcases p1562_3 (m.d 1 2) (by simp) with h1566 | h1566
                  · linarith only [h0, h1566, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1568 | h1568
                    · linarith only [h1568, hlam, p1562_0]
                    · rcases p1562_3 (m.d 1 4) (by simp) with h1570 | h1570
                      · linarith only [h1570, h2, hlam]
                      · linarith only [h1570, h941, hlam]
                · linarith only [h1565, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h1555, hc01, hlam, hphi, ht0b, ht5b, p1562_1, u5ehi4]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1575 | h1575
                · rcases p1562_3 (m.d 1 2) (by simp) with h1576 | h1576
                  · linarith only [h0, h1576, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1578 | h1578
                    · linarith only [h1, h1578, hlam]
                    · rcases p1562_3 (m.d 1 4) (by simp) with h1580 | h1580
                      · linarith only [h1580, h2, hlam]
                      · linarith only [h1555, h1580, hlam]
                · linarith only [h1575, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h0, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h10, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h866, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h939, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h1, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h0, h10, h1558, h1561, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h941, hlam, p1562_1]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h1553, hlam, p1562_1]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h2, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1595 | h1595
                · rcases p1562_3 (m.d 1 2) (by simp) with h1596 | h1596
                  · linarith only [h1596, h866, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1598 | h1598
                    · linarith only [h1598, h941, hlam]
                    · linarith only [h10, h1598, hlam]
                · linarith only [h0, h1595, hlam]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1602 | h1602
                · rcases p1562_3 (m.d 1 2) (by simp) with h1603 | h1603
                  · linarith only [h1603, h866, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1605 | h1605
                    · linarith only [h1605, h941, hlam]
                    · rcases p1562_3 (m.d 1 4) (by simp) with h1607 | h1607
                      · rcases p1562_3 (m.d 1 5) (by simp) with h1608 | h1608
                        · linarith only [h1555, h1608, hlam]
                        · linarith only [h1553, h1608, hlam]
                      · linarith only [h1607, h941, hlam]
                · linarith only [h1, h1602, hlam]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h2, hc01, hlam, hphi, ht0b, ht5b, p1562_1, u5ehi1]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h3, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1616 | h1616
                · rcases p1562_3 (m.d 1 2) (by simp) with h1617 | h1617
                  · linarith only [h1617, h939, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1619 | h1619
                    · linarith only [h1553, h1619, hlam]
                    · linarith only [h10, h1619, hlam]
                · linarith only [h0, h1616, hlam]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                rcases p1562_3 (m.d 0 1) (by simp) with h1623 | h1623
                · rcases p1562_3 (m.d 1 2) (by simp) with h1624 | h1624
                  · linarith only [h1624, h939, hlam]
                  · rcases p1562_3 (m.d 1 3) (by simp) with h1626 | h1626
                    · linarith only [h1553, h1626, hlam]
                    · rcases p1562_3 (m.d 1 4) (by simp) with h1628 | h1628
                      · rcases p1562_3 (m.d 1 5) (by simp) with h1629 | h1629
                        · rcases h1emax with h1630 | h1630 | h1630 | h1630 | h1630
                          · linarith only [h0, h1558, h1561, h1630, h4, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases h3bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1556, h1560, h7, h939, hlam, p1562_1, p1632_2]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              rcases p1632_3 (m.d 0 3) (by simp) with h1635 | h1635
                              · rcases p1632_3 (m.d 1 3) (by simp) with h1636 | h1636
                                · linarith only [h1, h1636, hlam]
                                · rcases p1632_3 (m.d 2 3) (by simp) with h1638 | h1638
                                  · linarith only [h1638, h4, hlam]
                                  · rcases p1632_3 (m.d 3 4) (by simp) with h1640 | h1640
                                    · linarith only [h1640, h7, hlam]
                                    · linarith only [h1556, h1640, hlam]
                              · linarith only [h1635, h4, hlam]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h0, h10, h1556, h1560, h4, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h0, h10, h1558, h4, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h10, hlam, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h941, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1553, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h4, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h10, h1556, hc12, hc34, hlam, hphi, ht23, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1556, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1558, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h7, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              rcases p1632_3 (m.d 0 3) (by simp) with h1657 | h1657
                              · rcases p1632_3 (m.d 1 3) (by simp) with h1658 | h1658
                                · linarith only [h1658, hlam, p1632_0]
                                · rcases p1632_3 (m.d 2 3) (by simp) with h1660 | h1660
                                  · linarith only [h1556, h1660, hlam]
                                  · linarith only [h10, h1660, hlam]
                              · linarith only [h1, h1657, hlam]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h0, h10, h1558, h4, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h8, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              rcases p1632_3 (m.d 0 3) (by simp) with h1668 | h1668
                              · rcases p1632_3 (m.d 1 3) (by simp) with h1669 | h1669
                                · linarith only [h1669, hlam, p1632_0]
                                · rcases p1632_3 (m.d 2 3) (by simp) with h1671 | h1671
                                  · linarith only [h1558, h1671, hlam]
                                  · linarith only [h10, h1671, hlam]
                              · linarith only [h1, h1668, hlam]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p1632_1]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [h1561, hlam, p1632_0]
                            · have p1632_0 := h1632c.1
                              have p1632_1 := h1632c.2.1
                              have p1632_2 := h1632c.2.2.1
                              have p1632_3 := h1632c.2.2.2
                              linarith only [hlam, p1632_0]
                          · rcases h3bigk with h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c | h1678c
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1553, h1561, h7, hlam, p1562_1, p1678_2]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              rcases p1678_3 (m.d 0 3) (by simp) with h1681 | h1681
                              · rcases p1678_3 (m.d 1 3) (by simp) with h1682 | h1682
                                · linarith only [h1, h1682, hlam]
                                · rcases p1678_3 (m.d 2 3) (by simp) with h1684 | h1684
                                  · linarith only [h1684, h4, hlam]
                                  · rcases p1678_3 (m.d 3 4) (by simp) with h1686 | h1686
                                    · linarith only [h1686, h7, hlam]
                                    · linarith only [h1556, h1686, hlam]
                              · linarith only [h1681, h4, hlam]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h10, h1556, h1560, h939, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h0, h10, h1558, h4, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h10, hlam, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h941, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1553, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h4, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h10, h1556, hc12, hc34, hlam, hphi, ht23, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1556, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1558, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h7, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              rcases p1678_3 (m.d 0 3) (by simp) with h1703 | h1703
                              · rcases p1678_3 (m.d 1 3) (by simp) with h1704 | h1704
                                · linarith only [h1704, hlam, p1678_0]
                                · rcases p1678_3 (m.d 2 3) (by simp) with h1706 | h1706
                                  · linarith only [h1556, h1706, hlam]
                                  · linarith only [h10, h1706, hlam]
                              · linarith only [h1, h1703, hlam]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h0, h10, h1558, h4, h7, h939, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1562_1, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h8, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              rcases p1678_3 (m.d 0 3) (by simp) with h1714 | h1714
                              · rcases p1678_3 (m.d 1 3) (by simp) with h1715 | h1715
                                · linarith only [h1715, hlam, p1678_0]
                                · rcases p1678_3 (m.d 2 3) (by simp) with h1717 | h1717
                                  · linarith only [h1558, h1717, hlam]
                                  · linarith only [h10, h1717, hlam]
                              · linarith only [h1, h1714, hlam]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p1678_1]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [h1561, hlam, p1678_0]
                            · have p1678_0 := h1678c.1
                              have p1678_1 := h1678c.2.1
                              have p1678_2 := h1678c.2.2.1
                              have p1678_3 := h1678c.2.2.2
                              linarith only [hlam, p1678_0]
                          · linarith only [h1555, h1630, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · linarith only [h10, h1630, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1562_1]
                        · linarith only [h1553, h1629, hlam]
                      · linarith only [h1628, h941, hlam]
                · linarith only [h1, h1623, hlam]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [h1555, hlam, p1562_0]
              · have p1562_0 := h1562c.1
                have p1562_1 := h1562c.2.1
                have p1562_2 := h1562c.2.2.1
                have p1562_3 := h1562c.2.2.2
                linarith only [hlam, p1562_0]
            · linarith only [h1555, h1561, h941, hlam]
          · linarith only [h1555, h1560, h866, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1733 | h1733
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1734 | h1734
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1735 | h1735
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1736 | h1736
            · linarith only [h0, h1555, h1733, h1736, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h10, h1733, h1735, h1736, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1739 | h1739
            · linarith only [h0, h1735, h1739, h4, h7, h866, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h1bigk with h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c | h1741c
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h10, h1733, h1735, h4, h7, h9, h941, hlam, p1741_2]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h1733, h1735, h4, h7, h9, h941, hlam, p1741_2]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                rcases p1741_3 (m.d 0 1) (by simp) with h1745 | h1745
                · rcases p1741_3 (m.d 1 2) (by simp) with h1746 | h1746
                  · linarith only [h0, h1746, hlam]
                  · rcases p1741_3 (m.d 1 3) (by simp) with h1748 | h1748
                    · linarith only [h1, h1748, hlam]
                    · rcases p1741_3 (m.d 1 4) (by simp) with h1750 | h1750
                      · linarith only [h1750, hlam, p1741_0]
                      · rcases p1741_3 (m.d 1 5) (by simp) with h1752 | h1752
                        · linarith only [h1752, h3, hlam]
                        · linarith only [h1555, h1752, hlam]
                · linarith only [h1745, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                rcases p1741_3 (m.d 0 1) (by simp) with h1756 | h1756
                · rcases p1741_3 (m.d 1 2) (by simp) with h1757 | h1757
                  · linarith only [h0, h1757, hlam]
                  · rcases p1741_3 (m.d 1 3) (by simp) with h1759 | h1759
                    · linarith only [h1, h1759, hlam]
                    · rcases p1741_3 (m.d 1 4) (by simp) with h1761 | h1761
                      · linarith only [h1761, h2, hlam]
                      · rcases p1741_3 (m.d 1 5) (by simp) with h1763 | h1763
                        · linarith only [h1763, hlam, p1741_0]
                        · rcases h1emax with h1765 | h1765 | h1765 | h1765 | h1765
                          · linarith only [h0, h10, h1733, h1735, h1765, h4, h7, h9, h941, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h3bigk with h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c | h1767c
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1733, h1735, h7, h9, h941, hlam, p1767_2]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hlam, hphi, ht0b, ht5b, p1767_1, u5ehi3]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              rcases p1767_3 (m.d 0 3) (by simp) with h1771 | h1771
                              · rcases p1767_3 (m.d 1 3) (by simp) with h1772 | h1772
                                · linarith only [h1, h1772, hlam]
                                · rcases p1767_3 (m.d 2 3) (by simp) with h1774 | h1774
                                  · linarith only [h1774, h4, hlam]
                                  · linarith only [h1733, h1774, hlam]
                              · linarith only [h1771, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              rcases p1767_3 (m.d 0 3) (by simp) with h1778 | h1778
                              · rcases p1767_3 (m.d 1 3) (by simp) with h1779 | h1779
                                · linarith only [h1, h1779, hlam]
                                · rcases p1767_3 (m.d 2 3) (by simp) with h1781 | h1781
                                  · linarith only [h1781, h4, hlam]
                                  · linarith only [h1734, h1781, hlam]
                              · linarith only [h1778, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h10, hlam, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h941, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1553, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h4, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              rcases p1767_3 (m.d 0 3) (by simp) with h1791 | h1791
                              · rcases p1767_3 (m.d 1 3) (by simp) with h1792 | h1792
                                · linarith only [h10, h1792, hlam]
                                · rcases p1767_3 (m.d 2 3) (by simp) with h1794 | h1794
                                  · rcases p1767_3 (m.d 3 4) (by simp) with h1795 | h1795
                                    · linarith only [h1733, h1795, hlam]
                                    · linarith only [h1795, h941, hlam]
                                  · linarith only [h10, h1794, hlam]
                              · linarith only [h1, h1791, hlam]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h10, h941, hc12, hc23, hlam, hphi, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h0, h10, h1739, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h7, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h0, h10, h1733, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1733, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1739, hlam, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h8, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h0, h10, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h1734, hlam, p1767_0]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [h10, h1734, h941, hc12, hc25, hlam, hphi, p1767_1]
                            · have p1767_0 := h1767c.1
                              have p1767_1 := h1767c.2.1
                              have p1767_2 := h1767c.2.2.1
                              have p1767_3 := h1767c.2.2.2
                              linarith only [hlam, p1767_0]
                          · rcases h3bigk with h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c | h1813c
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1733, h1735, h7, h9, h941, hlam, p1813_2]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hlam, hphi, ht0b, ht5b, p1813_1, u5ehi3]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              rcases p1813_3 (m.d 0 3) (by simp) with h1817 | h1817
                              · rcases p1813_3 (m.d 1 3) (by simp) with h1818 | h1818
                                · linarith only [h1, h1818, hlam]
                                · rcases p1813_3 (m.d 2 3) (by simp) with h1820 | h1820
                                  · linarith only [h1820, h4, hlam]
                                  · linarith only [h1733, h1820, hlam]
                              · linarith only [h1817, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              rcases p1813_3 (m.d 0 3) (by simp) with h1824 | h1824
                              · rcases p1813_3 (m.d 1 3) (by simp) with h1825 | h1825
                                · linarith only [h1, h1825, hlam]
                                · rcases p1813_3 (m.d 2 3) (by simp) with h1827 | h1827
                                  · linarith only [h1827, h4, hlam]
                                  · linarith only [h1734, h1827, hlam]
                              · linarith only [h1824, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h10, hlam, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h941, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1553, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h4, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              rcases p1813_3 (m.d 0 3) (by simp) with h1837 | h1837
                              · rcases p1813_3 (m.d 1 3) (by simp) with h1838 | h1838
                                · linarith only [h10, h1838, hlam]
                                · rcases p1813_3 (m.d 2 3) (by simp) with h1840 | h1840
                                  · rcases p1813_3 (m.d 3 4) (by simp) with h1841 | h1841
                                    · linarith only [h1733, h1841, hlam]
                                    · linarith only [h1841, h941, hlam]
                                  · linarith only [h10, h1840, hlam]
                              · linarith only [h1, h1837, hlam]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h10, h941, hc12, hc23, hlam, hphi, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h0, h10, h1739, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h7, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h0, h10, h1733, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1733, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1739, hlam, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h8, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h0, h10, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h1734, hlam, p1813_0]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1813_1]
                            · have p1813_0 := h1813c.1
                              have p1813_1 := h1813c.2.1
                              have p1813_2 := h1813c.2.2.1
                              have p1813_3 := h1813c.2.2.2
                              linarith only [hlam, p1813_0]
                          · rcases h3bigk with h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c | h1859c
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1733, h1735, h7, h9, h941, hlam, p1859_2]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hlam, hphi, ht0b, ht5b, p1859_1, u5ehi3]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              rcases p1859_3 (m.d 0 3) (by simp) with h1863 | h1863
                              · rcases p1859_3 (m.d 1 3) (by simp) with h1864 | h1864
                                · linarith only [h1, h1864, hlam]
                                · rcases p1859_3 (m.d 2 3) (by simp) with h1866 | h1866
                                  · linarith only [h1866, h4, hlam]
                                  · linarith only [h1733, h1866, hlam]
                              · linarith only [h1863, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              rcases p1859_3 (m.d 0 3) (by simp) with h1870 | h1870
                              · rcases p1859_3 (m.d 1 3) (by simp) with h1871 | h1871
                                · linarith only [h1, h1871, hlam]
                                · rcases p1859_3 (m.d 2 3) (by simp) with h1873 | h1873
                                  · linarith only [h1873, h4, hlam]
                                  · linarith only [h1734, h1873, hlam]
                              · linarith only [h1870, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h10, hlam, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h941, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1553, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h4, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              rcases p1859_3 (m.d 0 3) (by simp) with h1883 | h1883
                              · rcases p1859_3 (m.d 1 3) (by simp) with h1884 | h1884
                                · linarith only [h10, h1884, hlam]
                                · rcases p1859_3 (m.d 2 3) (by simp) with h1886 | h1886
                                  · rcases p1859_3 (m.d 3 4) (by simp) with h1887 | h1887
                                    · linarith only [h1733, h1887, hlam]
                                    · linarith only [h1887, h941, hlam]
                                  · linarith only [h10, h1886, hlam]
                              · linarith only [h1, h1883, hlam]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h10, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h10, h1553, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h7, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h10, h1733, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1733, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1739, hlam, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h8, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h10, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h1734, hlam, p1859_0]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1859_1]
                            · have p1859_0 := h1859c.1
                              have p1859_1 := h1859c.2.1
                              have p1859_2 := h1859c.2.2.1
                              have p1859_3 := h1859c.2.2.2
                              linarith only [hlam, p1859_0]
                          · rcases h3bigk with h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c | h1905c
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1733, h1735, h7, h9, h941, hlam, p1905_2]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hlam, hphi, ht0b, ht5b, p1905_1, u5ehi3]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              rcases p1905_3 (m.d 0 3) (by simp) with h1909 | h1909
                              · rcases p1905_3 (m.d 1 3) (by simp) with h1910 | h1910
                                · linarith only [h1, h1910, hlam]
                                · rcases p1905_3 (m.d 2 3) (by simp) with h1912 | h1912
                                  · linarith only [h1912, h4, hlam]
                                  · linarith only [h1733, h1912, hlam]
                              · linarith only [h1909, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              rcases p1905_3 (m.d 0 3) (by simp) with h1916 | h1916
                              · rcases p1905_3 (m.d 1 3) (by simp) with h1917 | h1917
                                · linarith only [h1, h1917, hlam]
                                · rcases p1905_3 (m.d 2 3) (by simp) with h1919 | h1919
                                  · linarith only [h1919, h4, hlam]
                                  · linarith only [h1734, h1919, hlam]
                              · linarith only [h1916, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h10, hlam, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h941, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1553, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h4, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              rcases p1905_3 (m.d 0 3) (by simp) with h1929 | h1929
                              · rcases p1905_3 (m.d 1 3) (by simp) with h1930 | h1930
                                · linarith only [h10, h1930, hlam]
                                · rcases p1905_3 (m.d 2 3) (by simp) with h1932 | h1932
                                  · rcases p1905_3 (m.d 3 4) (by simp) with h1933 | h1933
                                    · linarith only [h1733, h1933, hlam]
                                    · linarith only [h1933, h941, hlam]
                                  · linarith only [h10, h1932, hlam]
                              · linarith only [h1, h1929, hlam]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h10, h941, hc12, hc23, hlam, hphi, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h0, h10, h1739, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h7, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h0, h10, h1733, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1733, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1739, hlam, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h8, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h0, h10, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h1734, hlam, p1905_0]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [h0, h1734, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1905_1]
                            · have p1905_0 := h1905c.1
                              have p1905_1 := h1905c.2.1
                              have p1905_2 := h1905c.2.2.1
                              have p1905_3 := h1905c.2.2.2
                              linarith only [hlam, p1905_0]
                · linarith only [h1756, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h10, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h866, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h939, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h1, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h941, hc12, hc34, hlam, hphi, ht23, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h941, hlam, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h1553, hlam, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h2, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h1735, h4, h7, h866, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h1735, h4, h7, h866, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h1555, hlam, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h3, hlam, p1741_0]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h1553, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h10, h1553, h1734, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [h0, h1553, h1734, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1741_1]
              · have p1741_0 := h1741c.1
                have p1741_1 := h1741c.2.1
                have p1741_2 := h1741c.2.2.1
                have p1741_3 := h1741c.2.2.2
                linarith only [hlam, p1741_0]
        · linarith only [h0, h10, h1733, h1734, h4, h8, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1973 | h1973
        · linarith only [h1733, h1973, h7, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1975 | h1975
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1976 | h1976
            · rcases h1bigk with h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c | h1977c
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h10, h1973, h1976, h4, h7, hlam, p1977_2]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1733, h1975, h4, h7, h941, hlam, p1977_2]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1733, h1975, h4, h7, hlam, p1977_2]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                rcases p1977_3 (m.d 0 1) (by simp) with h1982 | h1982
                · rcases p1977_3 (m.d 1 2) (by simp) with h1983 | h1983
                  · linarith only [h0, h1983, hlam]
                  · rcases p1977_3 (m.d 1 3) (by simp) with h1985 | h1985
                    · linarith only [h1, h1985, hlam]
                    · rcases p1977_3 (m.d 1 4) (by simp) with h1987 | h1987
                      · linarith only [h1987, h2, hlam]
                      · rcases p1977_3 (m.d 1 5) (by simp) with h1989 | h1989
                        · linarith only [h1989, hlam, p1977_0]
                        · rcases h1emax with h1991 | h1991 | h1991 | h1991 | h1991
                          · linarith only [h0, h10, h1555, h1733, h1975, h1991, h4, h7, h941, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h3bigk with h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c | h1993c
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1555, h1733, h1975, h7, h941, hlam, p1993_2]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h1996 | h1996
                              · rcases p1993_3 (m.d 1 3) (by simp) with h1997 | h1997
                                · linarith only [h1, h1997, hlam]
                                · rcases p1993_3 (m.d 2 3) (by simp) with h1999 | h1999
                                  · linarith only [h1999, h4, hlam]
                                  · rcases p1993_3 (m.d 3 4) (by simp) with h2001 | h2001
                                    · linarith only [h2001, h7, hlam]
                                    · linarith only [h1733, h2001, hlam]
                              · linarith only [h1996, h4, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h10, h1555, h1733, h1975, h4, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h10, h1973, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h10, hlam, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h941, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1553, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h4, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h10, h1973, hc12, hc35, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1733, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1973, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h7, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2018 | h2018
                              · rcases p1993_3 (m.d 1 3) (by simp) with h2019 | h2019
                                · linarith only [h2019, hlam, p1993_0]
                                · rcases p1993_3 (m.d 2 3) (by simp) with h2021 | h2021
                                  · linarith only [h1733, h2021, hlam]
                                  · linarith only [h10, h2021, hlam]
                              · linarith only [h1, h2018, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht5b, p1993_1, u5ehi3]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h8, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              rcases p1993_3 (m.d 0 3) (by simp) with h2029 | h2029
                              · rcases p1993_3 (m.d 1 3) (by simp) with h2030 | h2030
                                · linarith only [h2030, hlam, p1993_0]
                                · rcases p1993_3 (m.d 2 3) (by simp) with h2032 | h2032
                                  · linarith only [h1973, h2032, hlam]
                                  · linarith only [h10, h2032, hlam]
                              · linarith only [h1, h2029, hlam]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p1993_1]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [h1976, hlam, p1993_0]
                            · have p1993_0 := h1993c.1
                              have p1993_1 := h1993c.2.1
                              have p1993_2 := h1993c.2.2.1
                              have p1993_3 := h1993c.2.2.2
                              linarith only [hlam, p1993_0]
                          · rcases h3bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1555, h1733, h1975, h7, h941, hlam, p2039_2]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              rcases p2039_3 (m.d 0 3) (by simp) with h2042 | h2042
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2043 | h2043
                                · linarith only [h1, h2043, hlam]
                                · rcases p2039_3 (m.d 2 3) (by simp) with h2045 | h2045
                                  · linarith only [h2045, h4, hlam]
                                  · rcases p2039_3 (m.d 3 4) (by simp) with h2047 | h2047
                                    · linarith only [h2047, h7, hlam]
                                    · linarith only [h1733, h2047, hlam]
                              · linarith only [h2042, h4, hlam]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h10, h1555, h1733, h1975, h941, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h0, h10, h1973, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h10, hlam, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h941, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1553, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h4, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h10, h1733, hc12, hc34, hlam, hphi, ht23, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1733, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1973, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h7, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              rcases p2039_3 (m.d 0 3) (by simp) with h2064 | h2064
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2065 | h2065
                                · linarith only [h2065, hlam, p2039_0]
                                · rcases p2039_3 (m.d 2 3) (by simp) with h2067 | h2067
                                  · linarith only [h1733, h2067, hlam]
                                  · linarith only [h10, h2067, hlam]
                              · linarith only [h1, h2064, hlam]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h0, h10, h1973, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h8, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              rcases p2039_3 (m.d 0 3) (by simp) with h2075 | h2075
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2076 | h2076
                                · linarith only [h2076, hlam, p2039_0]
                                · rcases p2039_3 (m.d 2 3) (by simp) with h2078 | h2078
                                  · linarith only [h1973, h2078, hlam]
                                  · linarith only [h10, h2078, hlam]
                              · linarith only [h1, h2075, hlam]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p2039_1]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [h1976, hlam, p2039_0]
                            · have p2039_0 := h2039c.1
                              have p2039_1 := h2039c.2.1
                              have p2039_2 := h2039c.2.2.1
                              have p2039_3 := h2039c.2.2.2
                              linarith only [hlam, p2039_0]
                          · rcases h3bigk with h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1555, h1733, h1975, h7, h941, hlam, p2085_2]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              rcases p2085_3 (m.d 0 3) (by simp) with h2088 | h2088
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2089 | h2089
                                · linarith only [h1, h2089, hlam]
                                · rcases p2085_3 (m.d 2 3) (by simp) with h2091 | h2091
                                  · linarith only [h2091, h4, hlam]
                                  · rcases p2085_3 (m.d 3 4) (by simp) with h2093 | h2093
                                    · linarith only [h2093, h7, hlam]
                                    · linarith only [h1733, h2093, hlam]
                              · linarith only [h2088, h4, hlam]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h10, h1555, h1733, h1975, h941, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h0, h10, h1973, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h10, hlam, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h941, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1553, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h4, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h10, h1733, hc12, hc34, hlam, hphi, ht23, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1733, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1973, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h7, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              rcases p2085_3 (m.d 0 3) (by simp) with h2110 | h2110
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2111 | h2111
                                · linarith only [h2111, hlam, p2085_0]
                                · rcases p2085_3 (m.d 2 3) (by simp) with h2113 | h2113
                                  · linarith only [h1733, h2113, hlam]
                                  · linarith only [h10, h2113, hlam]
                              · linarith only [h1, h2110, hlam]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h0, h10, h1973, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h8, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              rcases p2085_3 (m.d 0 3) (by simp) with h2121 | h2121
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2122 | h2122
                                · linarith only [h2122, hlam, p2085_0]
                                · rcases p2085_3 (m.d 2 3) (by simp) with h2124 | h2124
                                  · linarith only [h1973, h2124, hlam]
                                  · linarith only [h10, h2124, hlam]
                              · linarith only [h1, h2121, hlam]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p2085_1]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [h1976, hlam, p2085_0]
                            · have p2085_0 := h2085c.1
                              have p2085_1 := h2085c.2.1
                              have p2085_2 := h2085c.2.2.1
                              have p2085_3 := h2085c.2.2.2
                              linarith only [hlam, p2085_0]
                          · rcases h3bigk with h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c | h2131c
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1555, h1733, h1975, h7, h941, hlam, p2131_2]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              rcases p2131_3 (m.d 0 3) (by simp) with h2134 | h2134
                              · rcases p2131_3 (m.d 1 3) (by simp) with h2135 | h2135
                                · linarith only [h1, h2135, hlam]
                                · rcases p2131_3 (m.d 2 3) (by simp) with h2137 | h2137
                                  · linarith only [h2137, h4, hlam]
                                  · rcases p2131_3 (m.d 3 4) (by simp) with h2139 | h2139
                                    · linarith only [h2139, h7, hlam]
                                    · linarith only [h1733, h2139, hlam]
                              · linarith only [h2134, h4, hlam]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h10, h1555, h1733, h1975, h941, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h0, h10, h1973, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h10, hlam, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h941, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1553, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h4, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h10, h1733, hc12, hc34, hlam, hphi, ht23, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1733, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1973, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h7, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              rcases p2131_3 (m.d 0 3) (by simp) with h2156 | h2156
                              · rcases p2131_3 (m.d 1 3) (by simp) with h2157 | h2157
                                · linarith only [h2157, hlam, p2131_0]
                                · rcases p2131_3 (m.d 2 3) (by simp) with h2159 | h2159
                                  · linarith only [h1733, h2159, hlam]
                                  · linarith only [h10, h2159, hlam]
                              · linarith only [h1, h2156, hlam]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h0, h10, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h0, h10, h1973, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h8, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              rcases p2131_3 (m.d 0 3) (by simp) with h2167 | h2167
                              · rcases p2131_3 (m.d 1 3) (by simp) with h2168 | h2168
                                · linarith only [h2168, hlam, p2131_0]
                                · rcases p2131_3 (m.d 2 3) (by simp) with h2170 | h2170
                                  · linarith only [h1973, h2170, hlam]
                                  · linarith only [h10, h2170, hlam]
                              · linarith only [h1, h2167, hlam]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h10, hc12, hc35, hlam, hphi, ht23, p2131_1]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [h1976, hlam, p2131_0]
                            · have p2131_0 := h2131c.1
                              have p2131_1 := h2131c.2.1
                              have p2131_2 := h2131c.2.2.1
                              have p2131_3 := h2131c.2.2.2
                              linarith only [hlam, p2131_0]
                · linarith only [h1982, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h10, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h866, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h939, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h1, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h1555, h1975, h941, hc12, hc24, hlam, hphi, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h941, hlam, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h1553, hlam, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h2, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1975, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1975, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h1555, hlam, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h3, hlam, p1977_0]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1975, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h10, h1555, h1975, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [h0, h1555, h1975, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1977_1]
              · have p1977_0 := h1977c.1
                have p1977_1 := h1977c.2.1
                have p1977_2 := h1977c.2.2.1
                have p1977_3 := h1977c.2.2.2
                linarith only [hlam, p1977_0]
            · linarith only [h1733, h1975, h1976, hlam]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2199 | h2199
            · linarith only [h0, h10, h1733, h1975, h2199, h4, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h0, h10, h1733, h2199, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h939 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866 h939 h941
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866 h939 h941

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h866 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 5 (by decide) (by decide) with h939 | h939
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866 h939
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866 h939

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h866 | h866
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h866

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10

end R2N4
