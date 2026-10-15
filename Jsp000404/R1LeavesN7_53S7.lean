import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S5
import Jsp000404.R1LeavesN7_53S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1242 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1334 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h1576 | h1576
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1577 | h1577
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1578 | h1578
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1579 | h1579
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1580 | h1580
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1581 | h1581
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1583 | h1583
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1584 | h1584
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1585 | h1585
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1586 | h1586
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1587 | h1587
                        · linarith only [h1334, h1576, h1581, h1587, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1334, h1576, h1579, h1580, h1587, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1334, h1576, h1580, h1581, h1586, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1334, h1576, h1579, h1580, h1581, h1585, hlam]
                  · linarith only [h1334, h1576, h1578, h1581, h1584, hlam]
                · linarith only [h1334, h1577, h1581, h1583, hlam]
              · linarith only [h1334, h1576, h1581, h1582, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1595 | h1595
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1596 | h1596
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1597 | h1597
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1598 | h1598
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1599 | h1599
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1600 | h1600
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1601 | h1601
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1602 | h1602
                            · rcases h0bigk with h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c | h1603c
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, hlam, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h869, hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1088, hlam, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1242, hlam, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1581, hc01, hc23, hlam, hphi, ht12, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1334, hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1577, h1580, h1581, h1601, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1603_1, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1577, h1581, h1601, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1603_1, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                rcases p1603_3 (m.d 0 1) (by simp) with h1614 | h1614
                                · linarith only [h1614, h869, hlam]
                                · rcases p1603_3 (m.d 0 2) (by simp) with h1616 | h1616
                                  · linarith only [h1334, h1616, hlam]
                                  · linarith only [h0, h1616, hlam]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1576, h1600, h1602, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u0elo2, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1576, h1600, h1602, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u0elo2, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1577, h1601, hlam, hphi, ht0b, ht34, ht45, ht5b, p1603_1, u0elo2, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1576, h1581, hc01, hc23, hlam, hphi, ht12, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1576, hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1578, hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1576, h1577, h1581, h1601, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1603_1, u3ehi4]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h0, h1577, h1581, hc01, hc23, hlam, hphi, ht12, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1577, hlam, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1579, hlam, p1603_0]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [h1580, hlam, p1603_1]
                              · have p1603_0 := h1603c.1
                                have p1603_1 := h1603c.2.1
                                have p1603_2 := h1603c.2.2.1
                                have p1603_3 := h1603c.2.2.2
                                linarith only [hlam, p1603_0]
                            · linarith only [h0, h1576, h1580, h1581, h1602, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h0, h1581, h1601, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1334, h1576, h1579, h1580, h1600, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1088, h1580, h1599, hlam]
                    · linarith only [h1579, h1598, h869, hlam]
                  · linarith only [h1578, h1597, h869, hlam]
                · linarith only [h0, h1577, h1596, hlam]
              · linarith only [h0, h1576, h1595, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1641 | h1641
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1642 | h1642
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1643 | h1643
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1644 | h1644
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1645 | h1645
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1646 | h1646
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1647 | h1647
                        · linarith only [h1334, h1576, h1641, h1647, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1334, h1577, h1579, h1647, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1650 | h1650
                        · linarith only [h1334, h1576, h1641, h1650, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1334, h1577, h1579, h1650, hc34, hlam, hphi, u3ehi4]
                    · linarith only [h1334, h1577, h1579, h1641, h1645, hlam]
                  · linarith only [h1334, h1577, h1578, h1580, h1641, h1644, hlam]
                · linarith only [h1334, h1577, h1641, h1643, hlam]
              · linarith only [h1334, h1576, h1641, h1642, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1657 | h1657
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1658 | h1658
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1659 | h1659
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1660 | h1660
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1661 | h1661
                      · linarith only [h1578, h1580, h1641, h1657, h1661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1663 | h1663
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1664 | h1664
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1665 | h1665
                            · linarith only [h1576, h1661, h1663, h1665, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c | h1667c
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, hlam, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h869, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1088, hlam, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1242, hlam, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, h1641, hc01, hc23, hlam, hphi, ht12, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1334, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, h1576, h1641, h1663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1667_1, u3ehi3]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, h1576, h1580, h1641, h1663, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1667_1, u3ehi3]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                rcases p1667_3 (m.d 0 1) (by simp) with h1678 | h1678
                                · linarith only [h1678, h869, hlam]
                                · rcases p1667_3 (m.d 0 2) (by simp) with h1680 | h1680
                                  · linarith only [h1334, h1680, hlam]
                                  · linarith only [h0, h1680, hlam]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1576, h1663, hlam, hphi, ht0b, ht34, ht45, ht5b, p1667_1, u0elo2, u3ehi3]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1576, h1663, hlam, hphi, ht0b, ht34, ht45, ht5b, p1667_1, u0elo2, u3ehi3]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1576, h1580, h1663, hlam, hphi, ht0b, ht34, ht45, ht5b, p1667_1, u0elo2, u3ehi3]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1088, h1661, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1576, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1578, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1580, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, h1577, h1641, hc01, hc23, hlam, hphi, ht12, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1577, hlam, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h1579, hlam, p1667_0]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [h0, h1088, h1577, h1641, hc01, hc23, hlam, hphi, ht12, p1667_1]
                              · have p1667_0 := h1667c.1
                                have p1667_1 := h1667c.2.1
                                have p1667_2 := h1667c.2.2.1
                                have p1667_3 := h1667c.2.2.2
                                linarith only [hlam, p1667_0]
                          · linarith only [h0, h1641, h1664, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h1641, h1663, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1579, h1660, h869, hlam]
                  · linarith only [h1578, h1579, h1659, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                · linarith only [h0, h1577, h1658, hlam]
              · linarith only [h0, h1576, h1657, hlam]
        · linarith only [h1578, h1579, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1334, h1576, h1578, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1705 | h1705
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1706 | h1706
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1707 | h1707
          · linarith only [h1576, h1577, h1707, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1710 | h1710
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1711 | h1711
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1712 | h1712
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1713 | h1713
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1714 | h1714
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1715 | h1715
                        · linarith only [h1334, h1576, h1709, h1715, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1334, h1706, h1715, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1718 | h1718
                        · linarith only [h1334, h1576, h1709, h1718, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1334, h1705, h1718, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1705, h1713, h869, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1334, h1576, h1705, h1706, h1709, h1712, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                · linarith only [h1334, h1709, h1711, hc02, hc25, hlam, hphi]
              · linarith only [h1334, h1576, h1705, h1709, h1710, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1725 | h1725
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1726 | h1726
                · linarith only [h1576, h1577, h1705, h1709, h1726, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1728 | h1728
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1729 | h1729
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1730 | h1730
                      · linarith only [h1705, h1707, h1709, h1725, h1730, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1732 | h1732
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1733 | h1733
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1734 | h1734
                            · linarith only [h1576, h1730, h1732, h1734, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases h0bigk with h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c | h1736c
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h0, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h869, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1088, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1242, hlam, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h0, h1726, h1733, hc01, hc23, hlam, hphi, ht12, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1334, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h0, h1576, h1726, h1732, h1733, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1736_1, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1577, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                rcases p1736_3 (m.d 0 1) (by simp) with h1747 | h1747
                                · linarith only [h1747, h869, hlam]
                                · rcases p1736_3 (m.d 0 2) (by simp) with h1749 | h1749
                                  · linarith only [h1334, h1749, hlam]
                                  · linarith only [h0, h1749, hlam]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, h1732, hlam, hphi, ht0b, ht34, ht45, ht5b, p1736_1, u0elo2, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, h1732, hlam, hphi, ht0b, ht34, ht45, ht5b, p1736_1, u0elo2, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, h1577, h1732, hlam, hphi, ht0b, ht34, ht45, ht5b, p1736_1, u0elo2, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1088, h1730, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1736_1]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1705, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1707, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                rcases p1736_3 (m.d 0 1) (by simp) with h1761 | h1761
                                · linarith only [h1242, h1761, hlam]
                                · rcases p1736_3 (m.d 0 2) (by simp) with h1763 | h1763
                                  · linarith only [h1577, h1763, hlam]
                                  · linarith only [h0, h1763, hlam]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, h1732, hlam, hphi, ht0b, ht34, ht45, ht5b, p1736_1, u0elo4, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1706, hlam, p1736_0]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [h1576, h1706, h1732, hlam, hphi, ht0b, ht34, ht45, ht5b, p1736_1, u0elo2, u3ehi3]
                              · have p1736_0 := h1736c.1
                                have p1736_1 := h1736c.2.1
                                have p1736_2 := h1736c.2.2.1
                                have p1736_3 := h1736c.2.2.2
                                linarith only [hlam, p1736_0]
                          · linarith only [h1334, h1576, h1732, h1733, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h0, h1709, h1732, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h1706, h1729, h869, hlam]
                  · linarith only [h1576, h1705, h1706, h1728, h869, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
              · linarith only [h0, h1576, h1725, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · linarith only [h1705, h1706, hc35, hlam, hphi, u3ehi3]
      · linarith only [h1334, h1576, h1705, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h1777 | h1777
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1778 | h1778
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1779 | h1779
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1780 | h1780
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1781 | h1781
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1782 | h1782
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1783 | h1783
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1784 | h1784
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1785 | h1785
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1786 | h1786
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1787 | h1787
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1788 | h1788
                          · linarith only [h1576, h1777, h1781, h1787, h1788, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h1334, h1778, h1788, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1334, h1778, h1787, hlam]
                      · linarith only [h1576, h1777, h1780, h1782, h1786, hlam]
                    · linarith only [h1334, h1576, h1777, h1778, h1779, h1781, h1782, h1785, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1334, h1778, h1781, h1784, hlam]
                · linarith only [h1334, h1777, h1781, h1783, hlam]
              · linarith only [h1334, h1781, h1782, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1797 | h1797
              · linarith only [h1576, h1777, h1779, h1781, h1797, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1799 | h1799
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1800 | h1800
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1801 | h1801
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1802 | h1802
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1803 | h1803
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1804 | h1804
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1805 | h1805
                            · rcases h0bigk with h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c | h1806c
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h0, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h869, hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1088, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1242, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h0, h1797, h1803, hc01, hc23, hlam, hphi, ht12, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1334, hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1576, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h0, h1777, h1797, h1803, h1804, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1806_1, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                rcases p1806_3 (m.d 0 1) (by simp) with h1817 | h1817
                                · linarith only [h1817, h869, hlam]
                                · rcases p1806_3 (m.d 0 2) (by simp) with h1819 | h1819
                                  · linarith only [h1334, h1819, hlam]
                                  · linarith only [h0, h1819, hlam]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1777, h1804, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1, u0elo2, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1576, h1777, h1804, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1, u0elo2, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1777, h1804, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1, u0elo2, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                rcases p1806_3 (m.d 0 1) (by simp) with h1826 | h1826
                                · linarith only [h1088, h1826, hlam]
                                · rcases p1806_3 (m.d 0 2) (by simp) with h1828 | h1828
                                  · linarith only [h1576, h1828, hlam]
                                  · linarith only [h0, h1828, hlam]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1777, h1778, h1804, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1, u0elo2, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1778, hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1777, h1778, h1804, hlam, hphi, ht0b, ht34, ht45, ht5b, p1806_1, u0elo2, u3ehi4]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1242, h1797, h1799, h1803, hc01, hc23, hlam, hphi, ht12, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1777, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1779, hlam, p1806_0]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [h1780, hlam, p1806_1]
                              · have p1806_0 := h1806c.1
                                have p1806_1 := h1806c.2.1
                                have p1806_2 := h1806c.2.2.1
                                have p1806_3 := h1806c.2.2.2
                                linarith only [hlam, p1806_0]
                            · linarith only [h1778, h1780, h1805, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                          · linarith only [h0, h1797, h1803, h1804, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1334, h1779, h1803, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h0, h1088, h1777, h1780, h1781, h1802, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1779, h1801, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h1778, h1800, h869, hlam]
                · linarith only [h0, h1777, h1799, hlam]
          · linarith only [h1576, h1777, h1780, hlam]
        · linarith only [h1778, h1779, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1849 | h1849
        · linarith only [h1778, h1849, hc34, hlam, hphi, u3ehi4]
        · linarith only [h1334, h1777, h1849, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1852 | h1852
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1853 | h1853
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1854 | h1854
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1855 | h1855
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1856 | h1856
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1857 | h1857
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1858 | h1858
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1859 | h1859
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1860 | h1860
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1861 | h1861
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1862 | h1862
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1863 | h1863
                            · rcases h0bigk with h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c | h1864c
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h0, hlam, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h869, hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1088, hlam, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1242, hlam, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1576, h1855, h1861, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1334, hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1576, hlam, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1777, hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1334, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h0, h1334, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1088, h1334, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h0, h1334, h1777, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1576, h1855, h1861, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h0, h1576, h1855, h1861, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1852, hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1576, h1853, h1855, h1861, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1864_1, u3ehi4]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1334, h1853, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h0, h1334, h1853, h1855, hc01, hc12, hlam, hphi, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1853, hlam, p1864_0]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [h1854, hlam, p1864_1]
                              · have p1864_0 := h1864c.1
                                have p1864_1 := h1864c.2.1
                                have p1864_2 := h1864c.2.2.1
                                have p1864_3 := h1864c.2.2.2
                                linarith only [hlam, p1864_0]
                            · linarith only [h1576, h1854, h1855, h1861, h1863, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1334, h1852, h1862, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1334, h1852, h1861, hlam]
                      · linarith only [h1576, h1854, h1856, h1860, hlam]
                    · linarith only [h1334, h1853, h1855, h1859, hlam]
                  · linarith only [h1334, h1852, h1855, h1858, hlam]
                · linarith only [h1334, h1852, h1855, h1857, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1334, h1852, h1855, h1856, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1898 | h1898
              · linarith only [h0, h1576, h1855, h1898, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1900 | h1900
                · linarith only [h0, h1777, h1855, h1900, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1902 | h1902
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1903 | h1903
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1904 | h1904
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1905 | h1905
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1906 | h1906
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1907 | h1907
                            · rcases h0bigk with h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c | h1908c
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h0, hlam, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h869, hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1088, hlam, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1242, hlam, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h0, h1898, h1905, hc01, hc23, hlam, hphi, ht12, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1334, hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1576, hlam, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1777, hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1919 | h1919
                                · linarith only [h1919, h869, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1921 | h1921
                                  · linarith only [h1334, h1921, hlam]
                                  · linarith only [h0, h1921, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1924 | h1924
                                · linarith only [h1924, h869, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1926 | h1926
                                  · linarith only [h1334, h1926, hlam]
                                  · rcases p1908_3 (m.d 0 3) (by simp) with h1928 | h1928
                                    · rcases p1908_3 (m.d 0 4) (by simp) with h1929 | h1929
                                      · linarith only [h1852, h1929, hlam]
                                      · linarith only [h1576, h1929, hlam]
                                    · linarith only [h1334, h1928, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1852, h1907, hlam, hphi, ht0b, ht34, ht45, ht5b, p1908_1, u0elo2, u3ehi4]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1853, hlam, hphi, ht0b, ht34, ht45, ht5b, p1908_1, u0elo2, u3ehi4]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1936 | h1936
                                · linarith only [h1088, h1936, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1938 | h1938
                                  · linarith only [h1576, h1938, hlam]
                                  · linarith only [h0, h1938, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1941 | h1941
                                · linarith only [h1088, h1941, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1943 | h1943
                                  · linarith only [h1576, h1943, hlam]
                                  · rcases p1908_3 (m.d 0 3) (by simp) with h1945 | h1945
                                    · rcases p1908_3 (m.d 0 4) (by simp) with h1946 | h1946
                                      · rcases p1908_3 (m.d 0 5) (by simp) with h1947 | h1947
                                        · linarith only [h1854, h1947, hlam]
                                        · linarith only [h1777, h1947, hlam]
                                      · linarith only [h1576, h1946, hlam]
                                    · linarith only [h1334, h1945, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1852, hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1853, hlam, hphi, ht0b, ht34, ht45, ht5b, p1908_1, u0elo3, u3ehi4]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1955 | h1955
                                · linarith only [h1242, h1955, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1957 | h1957
                                  · linarith only [h1777, h1957, hlam]
                                  · linarith only [h0, h1957, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                rcases p1908_3 (m.d 0 1) (by simp) with h1960 | h1960
                                · linarith only [h1242, h1960, hlam]
                                · rcases p1908_3 (m.d 0 2) (by simp) with h1962 | h1962
                                  · linarith only [h1777, h1962, hlam]
                                  · rcases p1908_3 (m.d 0 3) (by simp) with h1964 | h1964
                                    · rcases p1908_3 (m.d 0 4) (by simp) with h1965 | h1965
                                      · rcases p1908_3 (m.d 0 5) (by simp) with h1966 | h1966
                                        · rcases h1bigk with h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c | h1967c
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h869, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1088, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1242, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1855, hc01, hc23, hlam, hphi, ht12, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1855, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1898, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1900, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            rcases p1967_3 (m.d 0 1) (by simp) with h1978 | h1978
                                            · linarith only [h1978, hlam, p1967_0]
                                            · rcases p1967_3 (m.d 1 2) (by simp) with h1980 | h1980
                                              · linarith only [h1855, h1980, hlam]
                                              · linarith only [h0, h1980, hlam]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, hc01, hc13, hlam, hphi, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1088, h1855, hc01, hc23, hlam, hphi, ht12, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, h1242, h1855, hc01, hc23, hlam, hphi, ht12, p1908_1, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            rcases p1967_3 (m.d 0 1) (by simp) with h1987 | h1987
                                            · linarith only [h1987, hlam, p1967_0]
                                            · rcases p1967_3 (m.d 1 2) (by simp) with h1989 | h1989
                                              · linarith only [h1898, h1989, hlam]
                                              · linarith only [h0, h1989, hlam]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, hc01, hc14, hlam, hphi, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1902, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, h1242, h1898, h1905, hc01, hc23, hlam, hphi, ht12, p1908_1, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            rcases p1967_3 (m.d 0 1) (by simp) with h1996 | h1996
                                            · linarith only [h1996, hlam, p1967_0]
                                            · rcases p1967_3 (m.d 1 2) (by simp) with h1998 | h1998
                                              · linarith only [h1900, h1998, hlam]
                                              · linarith only [h0, h1998, hlam]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h0, hc01, hc15, hlam, hphi, p1967_1]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1903, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [h1904, hlam, p1967_0]
                                          · have p1967_0 := h1967c.1
                                            have p1967_1 := h1967c.2.1
                                            have p1967_2 := h1967c.2.2.1
                                            have p1967_3 := h1967c.2.2.2
                                            linarith only [hlam, p1967_0]
                                        · linarith only [h1777, h1966, hlam]
                                      · linarith only [h1576, h1965, hlam]
                                    · linarith only [h1334, h1964, hlam]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1853, hlam, p1908_0]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [h1854, hlam, p1908_1]
                              · have p1908_0 := h1908c.1
                                have p1908_1 := h1908c.2.1
                                have p1908_2 := h1908c.2.2.1
                                have p1908_3 := h1908c.2.2.2
                                linarith only [hlam, p1908_0]
                            · linarith only [h1854, h1907, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h1852, h1855, h1906, h869, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1852, h1855, h1905, h869, hlam]
                      · linarith only [h1088, h1854, h1904, hlam]
                    · linarith only [h1853, h1903, h869, hlam]
                  · linarith only [h1852, h1902, h869, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2017 | h2017
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2018 | h2018
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2019 | h2019
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2020 | h2020
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2021 | h2021
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2022 | h2022
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2023 | h2023
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2024 | h2024
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2025 | h2025
                            · linarith only [h1852, h1854, h2025, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c | h2027c
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h0, hlam, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h869, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1088, hlam, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1242, hlam, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1576, h1854, h2020, h2022, hc01, hc13, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1576, hlam, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1777, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h0, h1334, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, h1852, h2017, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2027_1, u3ehi3]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, h1853, h2017, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2027_1, u3ehi4]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, h1852, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h0, h1334, h1852, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1852, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1854, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h0, h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1853, hlam, p2027_0]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [h1088, h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2027_1]
                              · have p2027_0 := h2027c.1
                                have p2027_1 := h2027c.2.1
                                have p2027_2 := h2027c.2.2.1
                                have p2027_3 := h2027c.2.2.2
                                linarith only [hlam, p2027_0]
                          · linarith only [h1334, h1852, h2024, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1334, h1852, h2023, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2055 | h2055
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2056 | h2056
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2057 | h2057
                            · linarith only [h0, h1334, h1576, h1852, h2017, h2018, h2022, h2057, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c | h2059c
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h0, hlam, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h869, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1088, hlam, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1242, hlam, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1576, h2018, hc01, hc14, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1334, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1576, hlam, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1777, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1334, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h0, h1334, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1088, h1334, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1242, h1334, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1088, h1334, h1853, h2017, h2022, h2057, hc01, hc12, hc45, hlam, hphi, ht34, p2059_1, u3ehi3]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h0, h1334, h1576, h1853, h2017, h2018, h2022, h2057, hc01, hc12, hc45, hlam, hphi, ht34, p2059_1, u3ehi3]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1852, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1854, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h0, h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1853, hlam, p2059_0]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [h1088, h1334, h1853, h2017, hc01, hc12, hlam, hphi, p2059_1]
                              · have p2059_0 := h2059c.1
                                have p2059_1 := h2059c.2.1
                                have p2059_2 := h2059c.2.2.1
                                have p2059_3 := h2059c.2.2.2
                                linarith only [hlam, p2059_0]
                          · linarith only [h1334, h1853, h2056, hlam]
                        · linarith only [h1334, h1852, h1853, h2055, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                    · linarith only [h1853, h2021, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h1334, h1852, h2017, h2020, hlam]
                · linarith only [h1334, h1852, h2017, h2019, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h1334, h1852, h2017, h2018, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2091 | h2091
              · linarith only [h0, h1576, h2017, h2091, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2093 | h2093
                · linarith only [h0, h1777, h2017, h2093, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2095 | h2095
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2096 | h2096
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2097 | h2097
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2098 | h2098
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2099 | h2099
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2100 | h2100
                            · linarith only [h1852, h1854, h2100, hlam]
                            · rcases h0bigk with h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c | h2102c
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h0, hlam, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h869, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1088, hlam, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1242, hlam, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h0, h2091, h2098, hc01, hc23, hlam, hphi, ht12, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1334, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1576, hlam, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1777, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                rcases p2102_3 (m.d 0 1) (by simp) with h2113 | h2113
                                · linarith only [h2113, h869, hlam]
                                · rcases p2102_3 (m.d 0 2) (by simp) with h2115 | h2115
                                  · linarith only [h1334, h2115, hlam]
                                  · linarith only [h0, h2115, hlam]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                rcases p2102_3 (m.d 0 1) (by simp) with h2118 | h2118
                                · linarith only [h2118, h869, hlam]
                                · rcases p2102_3 (m.d 0 2) (by simp) with h2120 | h2120
                                  · linarith only [h1334, h2120, hlam]
                                  · rcases p2102_3 (m.d 0 3) (by simp) with h2122 | h2122
                                    · rcases p2102_3 (m.d 0 4) (by simp) with h2123 | h2123
                                      · linarith only [h1852, h2123, hlam]
                                      · linarith only [h1576, h2123, hlam]
                                    · linarith only [h1334, h2122, hlam]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1852, hlam, hphi, ht0b, ht34, ht45, ht5b, p2102_1, u0elo2, u3ehi3]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1852, h1854, hlam, hphi, ht0b, ht34, ht45, ht5b, p2102_1, u0elo2, u3ehi3]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1854, h2095, h2097, hc01, hc13, hlam, hphi, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h0, h1854, h2095, h2097, hc01, hc13, hlam, hphi, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1852, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1854, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1854, h2095, h2097, hc01, hc13, hlam, hphi, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h0, h1854, h2095, h2097, hc01, hc13, hlam, hphi, p2102_1]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1853, hlam, p2102_0]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [h1852, h1854, h2095, h2097, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2102_1, u3ehi3]
                              · have p2102_0 := h2102c.1
                                have p2102_1 := h2102c.2.1
                                have p2102_2 := h2102c.2.2.1
                                have p2102_3 := h2102c.2.2.2
                                linarith only [hlam, p2102_0]
                          · linarith only [h0, h2091, h2098, h2099, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h1852, h1854, h2017, h2095, h2097, h2098, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2142 | h2142
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2143 | h2143
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2144 | h2144
                            · linarith only [h0, h1852, h2091, h2097, h2144, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                            · rcases h0bigk with h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c | h2146c
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h0, hlam, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h869, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1088, hlam, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1242, hlam, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h0, h2091, hc01, hc24, hlam, hphi, ht12, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1334, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1576, hlam, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1777, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                rcases p2146_3 (m.d 0 1) (by simp) with h2157 | h2157
                                · linarith only [h2157, h869, hlam]
                                · rcases p2146_3 (m.d 0 2) (by simp) with h2159 | h2159
                                  · linarith only [h1334, h2159, hlam]
                                  · linarith only [h0, h2159, hlam]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                rcases p2146_3 (m.d 0 1) (by simp) with h2162 | h2162
                                · linarith only [h2162, h869, hlam]
                                · rcases p2146_3 (m.d 0 2) (by simp) with h2164 | h2164
                                  · linarith only [h1334, h2164, hlam]
                                  · rcases p2146_3 (m.d 0 3) (by simp) with h2166 | h2166
                                    · rcases p2146_3 (m.d 0 4) (by simp) with h2167 | h2167
                                      · linarith only [h1852, h2167, hlam]
                                      · linarith only [h1576, h2167, hlam]
                                    · linarith only [h1334, h2166, hlam]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1852, hlam, hphi, ht0b, ht34, ht45, ht5b, p2146_1, u0elo2, u3ehi3]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1853, hlam, hphi, ht0b, ht34, ht45, ht5b, p2146_1, u0elo2, u3ehi4]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1088, h2097, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1088, h2097, hc02, hc45, hlam, hphi, ht23, ht34, p2146_1]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1852, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1854, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                rcases p2146_3 (m.d 0 1) (by simp) with h2179 | h2179
                                · linarith only [h1242, h2179, hlam]
                                · rcases p2146_3 (m.d 0 2) (by simp) with h2181 | h2181
                                  · linarith only [h1777, h2181, hlam]
                                  · linarith only [h0, h2181, hlam]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                rcases p2146_3 (m.d 0 1) (by simp) with h2184 | h2184
                                · linarith only [h1242, h2184, hlam]
                                · rcases p2146_3 (m.d 0 2) (by simp) with h2186 | h2186
                                  · linarith only [h1777, h2186, hlam]
                                  · rcases p2146_3 (m.d 0 3) (by simp) with h2188 | h2188
                                    · rcases p2146_3 (m.d 0 4) (by simp) with h2189 | h2189
                                      · linarith only [h1854, h2189, hlam]
                                      · linarith only [h1576, h2189, hlam]
                                    · linarith only [h1334, h2188, hlam]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1853, hlam, p2146_0]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [h1852, hlam, hphi, ht0b, ht34, ht45, ht5b, p2146_1, u0elo4, u3ehi3]
                              · have p2146_0 := h2146c.1
                                have p2146_1 := h2146c.2.1
                                have p2146_2 := h2146c.2.2.1
                                have p2146_3 := h2146c.2.2.2
                                linarith only [hlam, p2146_0]
                          · linarith only [h1852, h2017, h2143, h869, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h1852, h2017, h2142, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1853, h2096, h869, hlam]
                  · linarith only [h1852, h2095, h869, hlam]
        · linarith only [h1852, h1853, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h2201 | h2201
        · linarith only [h1852, h2201, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h2203 | h2203
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2204 | h2204
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2205 | h2205
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2206 | h2206
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2207 | h2207
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2208 | h2208
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2209 | h2209
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2210 | h2210
                        · linarith only [h1852, h2204, h2210, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h1334, h2204, h2207, h2210, hc01, hc12, hlam, hphi]
                      · linarith only [h1088, h2203, h2209, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2207, h2208, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2215 | h2215
                    · linarith only [h2207, h2215, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2217 | h2217
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2218 | h2218
                        · linarith only [h2207, h2218, h869, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2220 | h2220
                          · linarith only [h2204, h2215, h2220, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2222 | h2222
                            · rcases h0bigk with h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c | h2223c
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h0, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h869, hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1088, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1242, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1334, h2204, hc01, hc13, hlam, hphi, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1334, hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1576, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1777, hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h2215, h2222, h869, hc01, hc34, hlam, hphi, ht12, ht23, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1334, h2204, h2215, h2222, hc02, hc34, hlam, hphi, ht23, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1852, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h2201, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1576, h2205, hc01, hc12, hlam, hphi, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h0, h1576, h2205, hc01, hc12, hlam, hphi, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1576, h2205, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2223_1, u3ehi0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, p2223_0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1576, h2201, h2205, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2223_1, u3ehi0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h1576, h2203, h2205, hc01, hc12, hlam, hphi, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h0, h1576, h2203, h2205, hc01, hc12, hlam, hphi, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p2223_1, u0elo4, u3ehi0]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [h2203, hlam, p2223_1]
                              · have p2223_0 := h2223c.1
                                have p2223_1 := h2223c.2.1
                                have p2223_2 := h2223c.2.2.1
                                have p2223_3 := h2223c.2.2.2
                                linarith only [hlam, p2223_0]
                            · linarith only [h1576, h2203, h2205, h2222, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1088, h1576, h2203, h2205, h2217, hc01, hc12, hlam, hphi]
                · linarith only [h0, h1576, h2205, h2206, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1334, h2204, h2205, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2253 | h2253
              · linarith only [h0, h1576, h2204, h2253, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2255 | h2255
                · linarith only [h0, h1777, h2204, h2255, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2257 | h2257
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2258 | h2258
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2259 | h2259
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2260 | h2260
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2261 | h2261
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2262 | h2262
                            · rcases h0bigk with h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c | h2263c
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h0, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h869, hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1088, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1242, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h0, h2253, h2260, hc01, hc23, hlam, hphi, ht12, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1334, hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1576, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1777, hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2201, h2257, h2262, hc01, hc13, hlam, hphi, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2201, h2257, h2262, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1852, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2201, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1852, h2257, hc01, hc13, hlam, hphi, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h0, h1852, h2257, hc01, hc13, hlam, hphi, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1852, h2257, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2263_1, u3ehi0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [hlam, p2263_0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h1852, h2201, h2257, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2263_1, u3ehi0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2201, h2257, h2262, hc01, hc13, hlam, hphi, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h0, h2201, h2257, h2262, hc01, hc13, hlam, hphi, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2201, h2257, h2262, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p2263_1, u3ehi0]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [h2203, hlam, p2263_1]
                              · have p2263_0 := h2263c.1
                                have p2263_1 := h2263c.2.1
                                have p2263_2 := h2263c.2.2.1
                                have p2263_3 := h2263c.2.2.2
                                linarith only [hlam, p2263_0]
                            · linarith only [h1852, h2262, hc45, hlam, hphi, ht34, u3ehi0]
                          · linarith only [h1852, h2204, h2257, h2261, hc35, hlam, hphi, u3ehi0]
                        · linarith only [h2204, h2257, h2260, hlam]
                      · linarith only [h1088, h1852, h2203, h2204, h2257, h2259, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h1852, h2257, h2258, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2294 | h2294
                    · linarith only [h2257, h2294, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2296 | h2296
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2297 | h2297
                        · linarith only [h0, h2204, h2257, h2297, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h2204, h2297, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h1088, h2203, h2296, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h2301 | h2301
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2302 | h2302
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2303 | h2303
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2304 | h2304
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2305 | h2305
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2306 | h2306
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2307 | h2307
                        · linarith only [h1852, h2301, h2307, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h0, h1334, h2301, h2304, h2307, hc01, hc12, hlam, hphi]
                      · linarith only [h1852, h2304, h2306, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h1852, h2304, h2305, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2312 | h2312
                    · linarith only [h2304, h2312, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2314 | h2314
                      · linarith only [h1852, h2203, h2304, h2314, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2316 | h2316
                        · linarith only [h2301, h2304, h2314, h2316, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2318 | h2318
                          · linarith only [h2301, h2312, h2318, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2320 | h2320
                            · linarith only [h0, h1334, h2301, h2304, h2314, h2320, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h1852, h2320, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h1334, h2301, h2303, hc01, hc25, hlam, hphi, ht12]
              · linarith only [h0, h1334, h2301, h2302, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h2325 | h2325
              · linarith only [h0, h1576, h2301, h2325, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h2327 | h2327
                · linarith only [h0, h1777, h2301, h2327, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h2329 | h2329
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2330 | h2330
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2331 | h2331
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2332 | h2332
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h2333 | h2333
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2334 | h2334
                            · linarith only [h1852, h2203, h2334, hc34, hlam, hphi, u3ehi0]
                            · linarith only [h1852, h2301, h2329, h2331, h2334, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                          · linarith only [h2301, h2330, h2333, hlam]
                        · linarith only [h2301, h2330, h2332, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1852, h2329, h2331, hc45, hlam, hphi, ht34, u3ehi0]
                    · linarith only [h1852, h2329, h2330, hc35, hlam, hphi, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h2341 | h2341
                    · linarith only [h2329, h2341, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h2343 | h2343
                      · linarith only [h1852, h2203, h2329, h2343, hc34, hlam, hphi, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h2345 | h2345
                        · linarith only [h0, h2301, h2329, h2345, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h2301, h2345, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1242 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1334 | h1334
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h869 h1088 h1242 h1334
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h869 h1088 h1242 h1334

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1088 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1242 | h1242
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h869 h1088 h1242
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h869 h1088 h1242

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h869 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1088 | h1088
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x0 m hb0 hb1 hb3 hb4 h0 h869 h1088
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1_x1 m hb0 hb1 hb3 hb4 h0 h869 h1088

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h869 | h869
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x0 m hb0 hb1 hb3 hb4 h0 h869
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1_x1 m hb0 hb1 hb3 hb4 h0 h869

set_option maxHeartbeats 4696000 in
set_option maxHeartbeats 4696000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_M_LI_L_I_L_R_L_I_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
