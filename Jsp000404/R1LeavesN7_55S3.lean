import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S1
import Jsp000404.R1LeavesN7_55S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1211 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1563 | h1563
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1564 | h1564
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1565 | h1565
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1566 | h1566
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1567 | h1567
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1568 | h1568
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1569 | h1569
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1570 | h1570
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1571 | h1571
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1572 | h1572
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1573 | h1573
                      · linarith only [h1211, h1563, h1568, h1573, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                      · linarith only [h1211, h1563, h1567, h1568, h1569, h1573, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h1211, h1564, h1566, h1572, hc03, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1211, h1563, h1571, hlam]
                · linarith only [h1211, h1563, h1568, h1569, h1570, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1211, h1563, h1568, h1569, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
            · linarith only [h0, h1563, h1568, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1581 | h1581
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1583 | h1583
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1584 | h1584
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1585 | h1585
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1586 | h1586
                      · linarith only [h1211, h1563, h1567, h1581, h1586, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1588 | h1588
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1589 | h1589
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1590 | h1590
                            · linarith only [h1567, h1582, h1590, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1592 | h1592
                              · linarith only [h1563, h1567, h1582, h1588, h1592, hlam]
                              · rcases h5bigk with h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c | h1594c
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1211, h1564, h1581, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1211, h1564, h1581, h1589, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1211, h1564, h1581, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1567, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1564, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1589, hc35, hlam, hphi, ht01, ht0b, ht5b, p1594_1, u1elo4]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1211, h1564, h1581, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1586, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1565, hlam, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1583, hlam, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1594_1, u2elo4]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1590, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1566, hlam, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1585, hlam, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1589, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1592, hlam, p1594_0]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1563, h1567, h1582, h1588, hc34, hc45, hlam, hphi, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1582, h1586, h1588, hc34, hc45, hlam, hphi, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1588, h1590, hc34, hc45, hlam, hphi, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [h1592, hc34, hc45, hlam, hphi, p1594_1]
                                · have p1594_0 := h1594c.1
                                  have p1594_1 := h1594c.2.1
                                  have p1594_2 := h1594c.2.2.1
                                  have p1594_3 := h1594c.2.2.2
                                  linarith only [hlam, p1594_0]
                          · linarith only [h1211, h1564, h1581, h1585, h1589, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · linarith only [h1211, h1563, h1581, h1584, h1588, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h1211, h1566, h1585, hlam]
                  · linarith only [h1211, h1563, h1584, hlam]
                · linarith only [h1211, h1581, h1583, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h1563, h1581, h1582, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
            · linarith only [h0, h1563, h1581, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
        · linarith only [h1211, h1564, h1566, hlam]
      · linarith only [h0, h1564, h1565, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1629 | h1629
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1630 | h1630
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1631 | h1631
          · linarith only [h1563, h1564, h1631, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1633 | h1633
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1634 | h1634
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1635 | h1635
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1636 | h1636
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1637 | h1637
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1638 | h1638
                      · linarith only [h1563, h1564, h1631, h1633, h1637, h1638, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1640 | h1640
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1641 | h1641
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1642 | h1642
                            · linarith only [h1563, h1564, h1634, h1638, h1642, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1644 | h1644
                              · linarith only [h1563, h1564, h1634, h1638, h1640, h1644, hlam]
                              · rcases h5bigk with h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c | h1646c
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1564, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1629, h1641, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1211, h1630, h1633, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1631, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1633, h1637, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1633, h1637, h1641, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1633, h1637, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1638, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1629, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1635, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1646_1, u2elo4]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1642, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1630, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1637, hlam, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1641, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1644, hlam, p1646_0]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1563, h1564, h1634, h1640, hc34, hc45, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1563, h1564, h1634, h1640, hc34, hc45, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1640, h1642, hc34, hc45, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [h1644, hc34, hc45, hlam, hphi, p1646_1]
                                · have p1646_0 := h1646c.1
                                  have p1646_1 := h1646c.2.1
                                  have p1646_2 := h1646c.2.2.1
                                  have p1646_3 := h1646c.2.2.2
                                  linarith only [hlam, p1646_0]
                          · linarith only [h1211, h1630, h1633, h1640, h1641, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                        · linarith only [h1563, h1564, h1636, h1640, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
                    · linarith only [h1211, h1630, h1637, hlam]
                  · linarith only [h1211, h1563, h1636, hlam]
                · linarith only [h1211, h1633, h1635, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h1633, h1634, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1563, h1633, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1679 | h1679
          · linarith only [h1211, h1563, h1630, h1679, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1681 | h1681
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1682 | h1682
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1683 | h1683
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1684 | h1684
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1685 | h1685
                    · linarith only [h1211, h1630, h1681, h1685, hc01, hlam, hphi, ht12, u2elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1687 | h1687
                      · linarith only [h1563, h1679, h1687, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1689 | h1689
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1690 | h1690
                          · linarith only [h1211, h1681, h1685, h1690, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1692 | h1692
                            · linarith only [h1211, h1563, h1682, h1685, h1687, h1692, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1694 | h1694
                              · linarith only [h1211, h1563, h1682, h1685, h1687, h1689, h1694, hlam]
                              · linarith only [h1211, h1563, h1682, h1685, h1689, h1694, hc34, hc45, hlam, hphi]
                        · linarith only [h1684, h1685, h1689, hc23, hc35, hlam, hphi]
                  · linarith only [h1211, h1563, h1684, hlam]
                · linarith only [h1629, h1683, hc12, hlam, hphi, u2elo0]
              · linarith only [h1211, h1681, h1682, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1563, h1681, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1702 | h1702
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1703 | h1703
          · linarith only [h0, h1563, h1629, h1703, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1705 | h1705
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1706 | h1706
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1707 | h1707
                · linarith only [h0, h1629, h1707, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1563, h1706, h1707, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1211, h1705, h1706, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1563, h1705, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1712 | h1712
          · linarith only [h1211, h1563, h1702, h1712, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1714 | h1714
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1715 | h1715
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1716 | h1716
                · linarith only [h0, h1563, h1629, h1715, h1716, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                · linarith only [h0, h1563, h1715, h1716, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h1211, h1563, h1714, h1715, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
            · linarith only [h0, h1563, h1714, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1721 | h1721
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1722 | h1722
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1723 | h1723
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1724 | h1724
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1725 | h1725
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1726 | h1726
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1727 | h1727
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1729 | h1729
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1730 | h1730
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1731 | h1731
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1732 | h1732
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1733 | h1733
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1734 | h1734
                              · linarith only [h1725, h1731, h1734, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h1563, h1721, h1725, h1728, h1730, h1734, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · linarith only [h1563, h1721, h1725, h1728, h1730, h1733, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1563, h1721, h1725, h1728, h1729, h1732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1739 | h1739
                          · linarith only [h1725, h1728, h1731, h1739, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1563, h1721, h1725, h1728, h1729, h1739, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1563, h1721, h1724, h1730, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h1211, h1723, h1729, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1745 | h1745
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1746 | h1746
                        · linarith only [h1211, h1721, h1727, h1728, h1746, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1748 | h1748
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1749 | h1749
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1750 | h1750
                              · rcases h5bigk with h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c | h1751c
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1727, h1728, h1748, h1750, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1728, h1748, h1750, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1728, h1750, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1728, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1721, hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1748, h1750, hc45, hlam, hphi, ht01, ht0b, ht5b, p1751_1, u1elo4]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1728, h1750, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1728, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1722, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1727, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1750, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo4]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1211, h1721, h1726, h1727, h1728, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1723, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1744, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1748, hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [hlam, p1751_0]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1748, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1751_1, u2elo2]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1724, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1745, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1749, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [h1750, hlam, p1751_1]
                                · have p1751_0 := h1751c.1
                                  have p1751_1 := h1751c.2.1
                                  have p1751_2 := h1751c.2.2.1
                                  have p1751_3 := h1751c.2.2.2
                                  linarith only [hlam, p1751_0]
                              · linarith only [h1211, h1728, h1750, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h1211, h1721, h1726, h1728, h1745, h1746, h1749, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                          · linarith only [h1211, h1723, h1728, h1748, hc23, hc34, hlam, hphi]
                      · linarith only [h1563, h1724, h1745, hlam]
                    · linarith only [h1211, h1723, h1744, hlam]
                · linarith only [h0, h1721, h1727, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
              · linarith only [h1211, h1721, h1725, h1726, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
            · linarith only [h0, h1721, h1725, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
          · linarith only [h1563, h1721, h1724, hlam]
        · linarith only [h1211, h1721, h1723, hlam]
      · linarith only [h0, h1721, h1722, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h1788 | h1788
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1789 | h1789
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1790 | h1790
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1791 | h1791
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1792 | h1792
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1794 | h1794
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1795 | h1795
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1796 | h1796
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1797 | h1797
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1798 | h1798
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1799 | h1799
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1800 | h1800
                              · linarith only [h1791, h1797, h1800, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                              · linarith only [h1791, h1797, h1799, h1800, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1803 | h1803
                              · linarith only [h1797, h1799, h1803, hlam]
                              · rcases h5bigk with h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c | h1805c
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1721, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1788, h1797, h1799, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h0, h1788, h1803, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h0, h1788, h1797, h1799, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1805_1, u1elo4]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1793, h1797, h1799, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1791, h1795, h1803, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1791, h1794, h1796, h1797, h1799, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1788, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1793, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1803, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo4]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1799, hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1789, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1795, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1798, hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1803, hlam, p1805_0]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1790, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1796, hlam, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1790, hc04, hc25, hlam, hphi, ht0b, ht5b, p1805_1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [h1563, h1790, h1791, h1794, h1803, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1805_1, u2elo1]
                                · have p1805_0 := h1805c.1
                                  have p1805_1 := h1805c.2.1
                                  have p1805_2 := h1805c.2.2.1
                                  have p1805_3 := h1805c.2.2.2
                                  linarith only [hlam, p1805_0]
                          · linarith only [h1211, h1789, h1791, h1797, h1798, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1832 | h1832
                          · linarith only [h1791, h1794, h1797, h1832, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1834 | h1834
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1835 | h1835
                              · rcases h5bigk with h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c | h1836c
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hlam, p1836_0]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1721, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1721, h1791, h1794, h1796, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1721, h1791, h1794, h1796, h1832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1721, h1791, h1794, h1796, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1791, h1794, h1796, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hlam, p1836_0]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1791, h1794, h1796, h1834, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1791, h1794, h1796, h1832, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1791, h1794, h1796, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1788, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1793, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hlam, p1836_0]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1832, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo4]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1789, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1795, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1211, h1789, h1791, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hlam, p1836_0]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1721, h1789, h1791, h1794, h1796, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1836_1, u2elo1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1790, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1796, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1834, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [h1835, hlam, p1836_1]
                                · have p1836_0 := h1836c.1
                                  have p1836_1 := h1836c.2.1
                                  have p1836_2 := h1836c.2.2.1
                                  have p1836_3 := h1836c.2.2.2
                                  linarith only [hlam, p1836_0]
                              · linarith only [h1563, h1790, h1791, h1794, h1797, h1835, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                              · linarith only [h1791, h1794, h1797, h1834, h1863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · linarith only [h1563, h1790, h1791, h1794, h1797, h1863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h1563, h1790, h1796, hlam]
                    · linarith only [h1211, h1789, h1795, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1868 | h1868
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1869 | h1869
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1870 | h1870
                        · linarith only [h1211, h1789, h1794, h1870, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1872 | h1872
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1873 | h1873
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1874 | h1874
                              · rcases h5bigk with h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c | h1875c
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1721, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1211, h1789, h1794, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1211, h1789, h1794, h1874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1211, h1789, h1794, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1875_1, u1elo4]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1793, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1792, h1794, h1868, h1874, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1792, h1794, h1868, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1788, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1793, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1874, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo4]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo4]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1789, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1868, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1872, hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1872, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1875_1, u2elo2]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1790, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1869, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1873, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [h1874, hlam, p1875_1]
                                · have p1875_0 := h1875c.1
                                  have p1875_1 := h1875c.2.1
                                  have p1875_2 := h1875c.2.2.1
                                  have p1875_3 := h1875c.2.2.2
                                  linarith only [hlam, p1875_0]
                              · linarith only [h1211, h1794, h1874, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h1563, h1790, h1792, h1870, h1872, h1873, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1211, h1789, h1794, h1872, hc23, hc34, hlam, hphi]
                      · linarith only [h1563, h1790, h1869, hlam]
                    · linarith only [h1211, h1789, h1868, hlam]
                · linarith only [h0, h1793, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1792, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1791, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1909 | h1909
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1910 | h1910
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1911 | h1911
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1912 | h1912
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1913 | h1913
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1914 | h1914
                      · linarith only [h1563, h1790, h1914, hc01, hlam, hphi, u1elo3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1916 | h1916
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1917 | h1917
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1918 | h1918
                            · linarith only [h1563, h1909, h1914, h1916, h1918, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1920 | h1920
                              · linarith only [h1563, h1914, h1916, h1920, hc01, hlam, hphi, ht12, u2elo3]
                              · rcases h5bigk with h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c | h1922c
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1721, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1211, h1789, h1918, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1922_1, u1elo2]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1721, h1920, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1922_1, u1elo4]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1790, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1922_1, u1elo4]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1911, h1918, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1909, h1913, h1920, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1922_1, u2elo1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1914, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1788, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1911, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1920, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1922_1, u2elo4]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1918, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1789, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1913, hlam, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1917, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1920, hlam, p1922_0]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1721, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1721, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1917, h1920, hc34, hc45, hlam, hphi, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [h1920, hc34, hc45, hlam, hphi, p1922_1]
                                · have p1922_0 := h1922c.1
                                  have p1922_1 := h1922c.2.1
                                  have p1922_2 := h1922c.2.2.1
                                  have p1922_3 := h1922c.2.2.2
                                  linarith only [hlam, p1922_0]
                          · linarith only [h1211, h1789, h1909, h1916, h1917, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1949 | h1949
                          · linarith only [h1909, h1912, h1916, h1949, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1951 | h1951
                            · linarith only [h1563, h1790, h1951, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1953 | h1953
                              · linarith only [h1563, h1909, h1912, h1914, h1953, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases h5bigk with h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c | h1955c
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1721, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1721, h1951, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1955_1, u1elo4]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1211, h1789, h1909, h1916, h1953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1955_1, u2elo1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1790, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p1955_1, u1elo4]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1911, h1951, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1955_1, u2elo1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1909, h1913, h1916, h1953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1955_1, u2elo1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1914, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1788, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1911, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1949, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1951, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1789, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1913, hlam, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1916, h1951, hc23, hc35, hlam, hphi, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1953, hlam, p1955_0]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1721, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1721, h1909, h1912, h1916, hc01, hc23, hc45, hlam, hphi, ht12, ht34, p1955_1, u2elo1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1916, h1951, hc23, hc45, hlam, hphi, ht34, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [h1949, hc23, hc45, hlam, hphi, ht34, p1955_1]
                                · have p1955_0 := h1955c.1
                                  have p1955_1 := h1955c.2.1
                                  have p1955_2 := h1955c.2.2.1
                                  have p1955_3 := h1955c.2.2.2
                                  linarith only [hlam, p1955_0]
                    · linarith only [h1211, h1789, h1913, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1982 | h1982
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1983 | h1983
                      · linarith only [h1563, h1790, h1910, h1983, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1912, h1982, h1983, hlam]
                    · linarith only [h1211, h1789, h1982, hlam]
                · linarith only [h0, h1911, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h0, h1910, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1909, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1990 | h1990
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1991 | h1991
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1992 | h1992
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1993 | h1993
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1994 | h1994
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1995 | h1995
                    · linarith only [h1211, h1789, h1991, h1995, hc01, hlam, hphi, u1elo1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1997 | h1997
                      · linarith only [h1994, h1995, h1997, hlam]
                      · linarith only [h1563, h1990, h1997, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2000 | h2000
                    · linarith only [h1211, h1789, h2000, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2002 | h2002
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2003 | h2003
                        · linarith only [h1211, h1991, h1994, h2003, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2005 | h2005
                          · linarith only [h1211, h1992, h2000, h2003, h2005, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2007 | h2007
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2008 | h2008
                              · rcases h5bigk with h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c | h2009c
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1721, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1563, h1990, h1992, h2005, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2009_1, u2elo1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1789, hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1563, h1990, h1992, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2009_1, u2elo1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1992, h2002, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2009_1, u2elo1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1992, h2002, h2005, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2009_1, u2elo1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2000, hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1992, h2002, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2009_1, u2elo1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1788, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1993, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2005, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2009_1, u2elo4]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1211, h1789, h2008, hc01, hc34, hlam, hphi, ht12, ht23, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1721, h2008, hc01, hc34, hlam, hphi, ht12, ht23, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2005, h2008, hc23, hc34, hlam, hphi, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hlam, p2009_0]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  rcases p2009_3 (m.d 0 5) (by simp) with h2029 | h2029
                                  · linarith only [h1789, h2029, hlam]
                                  · linarith only [h1990, h2029, hlam]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h1990, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2002, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2007, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [h2008, hlam, p2009_1]
                                · have p2009_0 := h2009c.1
                                  have p2009_1 := h2009c.2.1
                                  have p2009_2 := h2009c.2.2.1
                                  have p2009_3 := h2009c.2.2.2
                                  linarith only [hlam, p2009_0]
                              · linarith only [h1211, h1994, h2008, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2038 | h2038
                              · rcases h5bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1721, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1563, h1990, h1992, h2003, h2007, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1789, hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1563, h1990, h1992, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1992, h2002, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1992, h2002, h2003, h2007, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2000, hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1992, h2002, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1788, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1993, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2005, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2007, hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1211, h1789, h2038, hc01, hc34, hlam, hphi, ht12, ht23, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1721, h2038, hc01, hc34, hlam, hphi, ht12, ht23, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2003, h2007, h2038, hc23, hc34, hlam, hphi, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [hlam, p2039_0]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2003, h2007, h2038, hc23, hc34, hlam, hphi, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1990, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2002, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h1563, h1990, h1992, h2003, h2007, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p2039_1, u2elo1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [h2038, hlam, p2039_1]
                                · have p2039_0 := h2039c.1
                                  have p2039_1 := h2039c.2.1
                                  have p2039_2 := h2039c.2.2.1
                                  have p2039_3 := h2039c.2.2.2
                                  linarith only [hlam, p2039_0]
                              · linarith only [h1211, h1563, h1990, h1992, h1994, h2038, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1563, h1990, h2002, hlam]
                · linarith only [h0, h1993, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h1991, h1992, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h1991, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2070 | h2070
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2071 | h2071
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2072 | h2072
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2073 | h2073
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2074 | h2074
                    · linarith only [h1211, h1789, h2074, hc01, hlam, hphi, u1elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2076 | h2076
                      · linarith only [h1563, h1990, h2072, h2073, h2074, h2076, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2078 | h2078
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2079 | h2079
                          · linarith only [h2070, h2074, h2079, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2081 | h2081
                            · linarith only [h0, h1563, h1788, h2076, h2078, h2079, h2081, hc01, hlam, hphi, ht12, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2083 | h2083
                              · linarith only [h0, h1563, h1788, h2076, h2078, h2079, h2083, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases h5bigk with h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1721, hlam, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2078, h2079, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1789, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1990, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2072, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p2085_1, u2elo1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2072, h2078, h2079, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2085_1, u2elo1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2074, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2076, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1788, hlam, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2072, hlam, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2079, hlam, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2081, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1788, h2078, h2079, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1721, h2083, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2078, h2079, h2083, hc34, hc45, hlam, hphi, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2083, hlam, p2085_0]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h1788, h2078, h2079, hc34, hc45, hlam, hphi, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h0, h1563, h1788, h2073, h2074, h2078, h2079, hc01, hc34, hc45, hlam, hphi, ht12, p2085_1, u2elo1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h2078, h2079, hc34, hc45, hlam, hphi, p2085_1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [h0, h1211, h1788, h1789, h2078, h2079, hc01, hc34, hc45, hlam, hphi, ht12, p2085_1, u2elo1]
                                · have p2085_0 := h2085c.1
                                  have p2085_1 := h2085c.2.1
                                  have p2085_2 := h2085c.2.2.1
                                  have p2085_3 := h2085c.2.2.2
                                  linarith only [hlam, p2085_0]
                        · linarith only [h2073, h2074, h2078, hc23, hc35, hlam, hphi]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2112 | h2112
                    · linarith only [h1211, h1789, h2073, h2112, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2114 | h2114
                      · linarith only [h1563, h1990, h2071, h2114, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2116 | h2116
                        · linarith only [h1211, h2073, h2116, hc01, hlam, hphi, ht12, u2elo2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2118 | h2118
                          · linarith only [h1211, h2112, h2118, hc01, hlam, hphi, ht12, u2elo2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h2120 | h2120
                            · linarith only [h2071, h2114, h2120, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h2122 | h2122
                              · linarith only [h1211, h2073, h2114, h2122, hc01, hc34, hlam, hphi, ht12, ht23]
                              · linarith only [h1211, h2073, h2122, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h1788, h2072, hlam]
              · linarith only [h0, h2071, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h2070, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2128 | h2128
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2129 | h2129
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2130 | h2130
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2131 | h2131
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2132 | h2132
                · linarith only [h1788, h2132, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h2132, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h2130, h2131, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h2130, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2137 | h2137
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2138 | h2138
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2139 | h2139
                · linarith only [h0, h1788, h2139, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h2139, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h2137, h2138, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h2137, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2144 | h2144
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2145 | h2145
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2146 | h2146
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2147 | h2147
                · linarith only [h0, h1788, h2147, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h2147, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h2145, h2146, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h2145, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2152 | h2152
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2153 | h2153
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2154 | h2154
                · linarith only [h0, h1788, h2154, hc01, hlam, hphi, u1elo1]
                · linarith only [h0, h2154, hc01, hlam, hphi, ht12, u2elo4]
              · linarith only [h1211, h2152, h2153, hc01, hlam, hphi, ht12, u2elo3]
            · linarith only [h0, h2152, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1211 | h1211
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1_x0 m hb1 hb2 hb4 hb5 h0 h1211
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1_x1 m hb1 hb2 hb4 hb5 h0 h1211

set_option maxHeartbeats 4318000 in
theorem r1l7_11_12_14_25_L_0_L_0_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_0_L_0_L_I_H_I_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
