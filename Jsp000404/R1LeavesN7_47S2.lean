import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1450 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1580 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h1581 | h1581
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1582 | h1582
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1583 | h1583
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1584 | h1584
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1585 | h1585
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1588 | h1588
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1589 | h1589
                  · linarith only [h1580, h1589, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1591 | h1591
                    · linarith only [h1581, h1589, h1591, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1593 | h1593
                      · linarith only [h1580, h1581, h1589, h1593, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1595 | h1595
                        · linarith only [h1580, h1581, h1593, h1595, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                        · rcases h1bigk with h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c | h1597c
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h0, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h903, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1345, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1450, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            rcases p1597_3 (m.d 0 1) (by simp) with h1603 | h1603
                            · linarith only [h1603, hlam, p1597_0]
                            · rcases p1597_3 (m.d 1 2) (by simp) with h1605 | h1605
                              · rcases p1597_3 (m.d 1 3) (by simp) with h1606 | h1606
                                · linarith only [h1583, h1606, hlam]
                                · linarith only [h1606, h903, hlam]
                              · linarith only [h1605, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1586, h1588, h1589, h1595, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1588, h1589, h1595, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            rcases p1597_3 (m.d 0 1) (by simp) with h1614 | h1614
                            · linarith only [h1614, hlam, p1597_0]
                            · rcases p1597_3 (m.d 1 2) (by simp) with h1616 | h1616
                              · rcases p1597_3 (m.d 1 3) (by simp) with h1617 | h1617
                                · rcases p1597_3 (m.d 1 4) (by simp) with h1618 | h1618
                                  · linarith only [h1586, h1618, hlam]
                                  · linarith only [h1345, h1618, hlam]
                                · linarith only [h1617, hlam, p1597_0]
                              · linarith only [h0, h1616, hlam]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1583, hlam, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1588, h1589, h1595, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1583, h1588, h1589, h1595, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            rcases p1597_3 (m.d 0 1) (by simp) with h1627 | h1627
                            · linarith only [h1627, hlam, p1597_0]
                            · rcases p1597_3 (m.d 1 2) (by simp) with h1629 | h1629
                              · rcases p1597_3 (m.d 1 3) (by simp) with h1630 | h1630
                                · rcases p1597_3 (m.d 1 4) (by simp) with h1631 | h1631
                                  · rcases p1597_3 (m.d 1 5) (by simp) with h1632 | h1632
                                    · linarith only [h1588, h1632, hlam]
                                    · linarith only [h1450, h1632, hlam]
                                  · linarith only [h1631, hlam, p1597_0]
                                · linarith only [h1630, h903, hlam]
                              · linarith only [h0, h1629, hlam]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1584, hlam, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1586, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1588, h1589, h1595, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            rcases p1597_3 (m.d 0 1) (by simp) with h1642 | h1642
                            · linarith only [h1642, hlam, p1597_0]
                            · rcases p1597_3 (m.d 1 2) (by simp) with h1644 | h1644
                              · rcases p1597_3 (m.d 1 3) (by simp) with h1645 | h1645
                                · rcases p1597_3 (m.d 1 4) (by simp) with h1646 | h1646
                                  · rcases p1597_3 (m.d 1 5) (by simp) with h1647 | h1647
                                    · rcases h3bigk with h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c | h1648c
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h903, hlam, p1648_1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        rcases p1648_3 (m.d 0 3) (by simp) with h1651 | h1651
                                        · rcases p1648_3 (m.d 1 3) (by simp) with h1652 | h1652
                                          · rcases p1648_3 (m.d 2 3) (by simp) with h1653 | h1653
                                            · linarith only [h1580, h1653, hlam]
                                            · rcases p1648_3 (m.d 3 4) (by simp) with h1655 | h1655
                                              · linarith only [h1581, h1655, hlam]
                                              · linarith only [h1589, h1655, hlam]
                                          · linarith only [h1583, h1652, hlam]
                                        · linarith only [h1580, h1651, hlam]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1580, h1589, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1648_1, u0elo1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1580, h1589, h1595, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1648_1, u0elo1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1581, h1583, h1589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1648_1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1586, h1588, h1589, h1595, hlam, p1648_2]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        rcases p1648_3 (m.d 0 3) (by simp) with h1665 | h1665
                                        · linarith only [h1665, h903, hlam]
                                        · linarith only [h1581, h1665, hlam]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        rcases p1648_3 (m.d 0 3) (by simp) with h1668 | h1668
                                        · linarith only [h1668, h903, hlam]
                                        · linarith only [h1582, h1668, hlam]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1580, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1583, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1589, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1591, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1581, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1586, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1582, h1595, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1648_1, u0elo2]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1595, hlam, p1648_1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1582, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1587, hlam, p1648_0]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1580, h1582, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1648_1, u0elo1]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [h1580, h1582, hlam, hphi, ht0b, ht45, ht5b, p1648_1, u0elo1, u4ehi3]
                                      · have p1648_0 := h1648c.1
                                        have p1648_1 := h1648c.2.1
                                        have p1648_2 := h1648c.2.2.1
                                        have p1648_3 := h1648c.2.2.2
                                        linarith only [hlam, p1648_0]
                                    · linarith only [h1647, hlam, p1597_0]
                                  · linarith only [h1345, h1646, hlam]
                                · linarith only [h1645, h903, hlam]
                              · linarith only [h0, h1644, hlam]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1585, hlam, p1597_1]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1587, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [h1588, hlam, p1597_0]
                          · have p1597_0 := h1597c.1
                            have p1597_1 := h1597c.2.1
                            have p1597_2 := h1597c.2.2.1
                            have p1597_3 := h1597c.2.2.2
                            linarith only [hlam, p1597_0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1694 | h1694
                  · linarith only [h1580, h1694, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1696 | h1696
                    · linarith only [h1580, h1581, h1694, h1696, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1698 | h1698
                      · linarith only [h1345, h1588, h1698, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1700 | h1700
                        · linarith only [h1345, h1581, h1588, h1700, hlam]
                        · rcases h1bigk with h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c | h1702c
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h0, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h903, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1345, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1450, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            rcases p1702_3 (m.d 0 1) (by simp) with h1708 | h1708
                            · linarith only [h1708, hlam, p1702_0]
                            · rcases p1702_3 (m.d 1 2) (by simp) with h1710 | h1710
                              · rcases p1702_3 (m.d 1 3) (by simp) with h1711 | h1711
                                · linarith only [h1583, h1711, hlam]
                                · linarith only [h1711, h903, hlam]
                              · linarith only [h1710, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h903, hc01, hc12, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1345, hc01, hc12, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            rcases p1702_3 (m.d 0 1) (by simp) with h1719 | h1719
                            · linarith only [h1719, hlam, p1702_0]
                            · rcases p1702_3 (m.d 1 2) (by simp) with h1721 | h1721
                              · rcases p1702_3 (m.d 1 3) (by simp) with h1722 | h1722
                                · rcases p1702_3 (m.d 1 4) (by simp) with h1723 | h1723
                                  · linarith only [h1586, h1723, hlam]
                                  · linarith only [h1345, h1723, hlam]
                                · linarith only [h1722, hlam, p1702_0]
                              · linarith only [h0, h1721, hlam]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1583, hlam, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1345, hc01, hc13, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1345, h1583, h1588, hc01, hc12, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1588, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1584, hlam, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1586, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1588, hlam, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            rcases p1702_3 (m.d 0 1) (by simp) with h1737 | h1737
                            · linarith only [h1737, hlam, p1702_0]
                            · rcases p1702_3 (m.d 1 2) (by simp) with h1739 | h1739
                              · rcases p1702_3 (m.d 1 3) (by simp) with h1740 | h1740
                                · rcases p1702_3 (m.d 1 4) (by simp) with h1741 | h1741
                                  · linarith only [h1588, h1741, hlam]
                                  · linarith only [h1345, h1741, hlam]
                                · linarith only [h1740, h903, hlam]
                              · linarith only [h0, h1739, hlam]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1585, hlam, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1587, hlam, p1702_0]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [h1345, hc01, hc15, hlam, hphi, p1702_1]
                          · have p1702_0 := h1702c.1
                            have p1702_1 := h1702c.2.1
                            have p1702_2 := h1702c.2.2.1
                            have p1702_3 := h1702c.2.2.2
                            linarith only [hlam, p1702_0]
              · linarith only [h1580, h1582, h1587, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h1581, h1586, h903, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1752 | h1752
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1753 | h1753
              · linarith only [h1583, h1585, h1753, hlam]
              · linarith only [h0, h1580, h1582, h1585, h1753, h903, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h1581, h1752, h903, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1757 | h1757
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1758 | h1758
            · linarith only [h1583, h1584, h1758, hlam]
            · linarith only [h1580, h1581, h1758, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1761 | h1761
            · linarith only [h1583, h1584, h1761, hlam]
            · linarith only [h0, h1580, h1581, h1584, h1761, h903, hc01, hc24, hlam, hphi, ht12]
      · linarith only [h0, h1580, h1583, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1765 | h1765
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1766 | h1766
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1767 | h1767
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1768 | h1768
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1769 | h1769
              · linarith only [h1581, h1582, h1769, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1771 | h1771
                · linarith only [h1768, h1769, h1771, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1773 | h1773
                  · linarith only [h1580, h1773, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · linarith only [h1581, h1769, h1773, h903, hc23, hc35, hlam, hphi]
            · linarith only [h1581, h1768, h903, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1777 | h1777
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1778 | h1778
              · linarith only [h1581, h1582, h1778, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1780 | h1780
                · linarith only [h1766, h1767, h1780, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1782 | h1782
                  · linarith only [h0, h1580, h1767, h1782, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h1581, h1778, h1782, h903, hc23, hc35, hlam, hphi]
            · linarith only [h1581, h1777, h903, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1786 | h1786
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1787 | h1787
            · linarith only [h1765, h1766, h1787, hlam]
            · linarith only [h1581, h1582, h1787, hc13, hc35, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1790 | h1790
            · linarith only [h1765, h1766, h1790, hlam]
            · linarith only [h1581, h1582, h1790, hc13, hc35, hlam, hphi]
      · linarith only [h0, h1580, h1765, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1794 | h1794
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1795 | h1795
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1796 | h1796
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1797 | h1797
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1798 | h1798
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1799 | h1799
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1800 | h1800
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1801 | h1801
                  · linarith only [h1580, h1581, h1801, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1803 | h1803
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1804 | h1804
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1805 | h1805
                        · linarith only [h1580, h1581, h1795, h1798, h1803, h1805, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h1580, h1581, h1795, h1798, h1800, h1803, h1805, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h1801, h1803, h1804, hlam]
                    · linarith only [h1581, h1794, h1803, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1810 | h1810
                  · linarith only [h1580, h1581, h1794, h1810, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1812 | h1812
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1813 | h1813
                      · linarith only [h1580, h1581, h1798, h1800, h1812, h1813, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h1580, h1581, h1798, h1800, h1812, h1813, hc45, hlam, hphi, u4ehi2]
                    · linarith only [h1581, h1794, h1798, h1800, h1812, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h1581, h1794, h1799, hc13, hc34, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1818 | h1818
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1819 | h1819
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1820 | h1820
                  · linarith only [h1798, h1820, h903, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1822 | h1822
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1823 | h1823
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1824 | h1824
                        · linarith only [h1580, h1822, h1824, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                        · linarith only [h1450, h1798, h1818, h1823, h1824, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h1820, h1822, h1823, hlam]
                    · linarith only [h1794, h1798, h1822, h903, hc23, hc34, hlam, hphi]
                · linarith only [h1798, h1818, h1819, hlam]
              · linarith only [h1794, h1818, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1831 | h1831
            · linarith only [h1581, h1794, h1795, h1797, h1831, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1833 | h1833
              · linarith only [h1795, h1797, h1833, hlam]
              · linarith only [h1794, h1833, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1836 | h1836
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1837 | h1837
            · linarith only [h1581, h1794, h1795, h1796, h1837, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1839 | h1839
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1840 | h1840
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1841 | h1841
                  · linarith only [h1450, h1837, h1839, h1841, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1843 | h1843
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1844 | h1844
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1845 | h1845
                        · linarith only [h0, h1580, h1796, h1841, h1843, h1845, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h1580, h1796, h1841, h1843, h1844, h1845, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h1580, h1796, h1840, h1843, h1844, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h1580, h1794, h1796, h1841, h1843, hc23, hc34, hlam, hphi]
                · linarith only [h1795, h1796, h1839, h1840, hlam]
              · linarith only [h0, h1580, h1794, h1796, h1839, h903, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1852 | h1852
            · linarith only [h1581, h1794, h1795, h1796, h1852, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1854 | h1854
              · linarith only [h1795, h1836, h1854, hlam]
              · linarith only [h1794, h1854, h903, hlam]
      · linarith only [h0, h1580, h1795, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1858 | h1858
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1859 | h1859
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1860 | h1860
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1861 | h1861
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1862 | h1862
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1863 | h1863
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1864 | h1864
                  · linarith only [h1580, h1581, h1864, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1866 | h1866
                    · linarith only [h1450, h1580, h1581, h1794, h1858, h1861, h1866, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1868 | h1868
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1869 | h1869
                        · rcases h1bigk with h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c | h1870c
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h0, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h903, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1345, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1450, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            rcases p1870_3 (m.d 0 1) (by simp) with h1876 | h1876
                            · linarith only [h1876, hlam, p1870_0]
                            · rcases p1870_3 (m.d 1 2) (by simp) with h1878 | h1878
                              · rcases p1870_3 (m.d 1 3) (by simp) with h1879 | h1879
                                · linarith only [h1858, h1879, hlam]
                                · linarith only [h1879, h903, hlam]
                              · linarith only [h1878, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1794, h1861, h1869, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1794, h1862, h1863, h903, hc01, hc12, hlam, hphi, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1794, h1862, h903, hc01, hc12, hlam, hphi, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            rcases p1870_3 (m.d 0 1) (by simp) with h1887 | h1887
                            · linarith only [h1887, hlam, p1870_0]
                            · rcases p1870_3 (m.d 1 2) (by simp) with h1889 | h1889
                              · rcases p1870_3 (m.d 1 3) (by simp) with h1890 | h1890
                                · rcases p1870_3 (m.d 1 4) (by simp) with h1891 | h1891
                                  · linarith only [h1861, h1891, hlam]
                                  · linarith only [h1345, h1891, hlam]
                                · linarith only [h1890, hlam, p1870_0]
                              · linarith only [h0, h1889, hlam]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1858, hlam, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1861, h1864, h1868, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1870_1, u4ehi4]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1794, h1858, h1862, h903, hc01, hc12, hlam, hphi, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            rcases p1870_3 (m.d 0 1) (by simp) with h1900 | h1900
                            · linarith only [h1900, hlam, p1870_0]
                            · rcases p1870_3 (m.d 1 2) (by simp) with h1902 | h1902
                              · rcases p1870_3 (m.d 1 3) (by simp) with h1903 | h1903
                                · rcases p1870_3 (m.d 1 4) (by simp) with h1904 | h1904
                                  · rcases p1870_3 (m.d 1 5) (by simp) with h1905 | h1905
                                    · linarith only [h1863, h1905, hlam]
                                    · linarith only [h1450, h1905, hlam]
                                  · linarith only [h1904, hlam, p1870_0]
                                · linarith only [h1903, h903, hlam]
                              · linarith only [h0, h1902, hlam]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1859, hlam, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1861, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1794, h1862, h903, hc01, hc14, hlam, hphi, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            rcases p1870_3 (m.d 0 1) (by simp) with h1915 | h1915
                            · linarith only [h1915, hlam, p1870_0]
                            · rcases p1870_3 (m.d 1 2) (by simp) with h1917 | h1917
                              · rcases p1870_3 (m.d 1 3) (by simp) with h1918 | h1918
                                · rcases p1870_3 (m.d 1 4) (by simp) with h1919 | h1919
                                  · rcases p1870_3 (m.d 1 5) (by simp) with h1920 | h1920
                                    · rcases h3bigk with h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c | h1921c
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h903, hlam, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1794, hc23, hc35, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1581, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1794, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        rcases p1921_3 (m.d 0 3) (by simp) with h1927 | h1927
                                        · linarith only [h1927, h903, hlam]
                                        · rcases p1921_3 (m.d 1 3) (by simp) with h1929 | h1929
                                          · rcases p1921_3 (m.d 2 3) (by simp) with h1930 | h1930
                                            · linarith only [h1858, h1930, hlam]
                                            · rcases p1921_3 (m.d 3 4) (by simp) with h1932 | h1932
                                              · linarith only [h1861, h1932, hlam]
                                              · linarith only [h1581, h1932, hlam]
                                          · linarith only [h1929, h903, hlam]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        rcases p1921_3 (m.d 0 3) (by simp) with h1937 | h1937
                                        · linarith only [h1937, h903, hlam]
                                        · linarith only [h1580, h1937, hlam]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1794, h1858, h1869, h903, hc01, hc12, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1794, h1858, h903, hc01, hc12, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1580, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1858, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1864, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1866, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1858, h1861, h903, hc01, hc12, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1861, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        rcases p1921_3 (m.d 0 3) (by simp) with h1949 | h1949
                                        · linarith only [h1581, h1949, hlam]
                                        · linarith only [h1580, h1949, hlam]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1794, h1858, h1861, h903, hc01, hc12, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1858, h1862, h903, hc01, hc12, hlam, hphi, p1921_1]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1862, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        rcases p1921_3 (m.d 0 3) (by simp) with h1956 | h1956
                                        · linarith only [h1794, h1956, hlam]
                                        · linarith only [h1580, h1956, hlam]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [h1869, hlam, p1921_0]
                                      · have p1921_0 := h1921c.1
                                        have p1921_1 := h1921c.2.1
                                        have p1921_2 := h1921c.2.2.1
                                        have p1921_3 := h1921c.2.2.2
                                        linarith only [hlam, p1921_0]
                                    · linarith only [h1920, hlam, p1870_0]
                                  · linarith only [h1345, h1919, hlam]
                                · linarith only [h1918, h903, hlam]
                              · linarith only [h0, h1917, hlam]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1860, hlam, p1870_1]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1862, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [h1863, hlam, p1870_0]
                          · have p1870_0 := h1870c.1
                            have p1870_1 := h1870c.2.1
                            have p1870_2 := h1870c.2.2.1
                            have p1870_3 := h1870c.2.2.2
                            linarith only [hlam, p1870_0]
                        · linarith only [h1581, h1858, h1861, h1863, h1869, h903, hc01, hc12, hlam, hphi]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1970 | h1970
                        · linarith only [h1858, h1861, h1868, h1970, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h1581, h1858, h1861, h1863, h1970, h903, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1973 | h1973
                  · linarith only [h1580, h1581, h1973, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1975 | h1975
                    · linarith only [h1580, h1794, h1975, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1977 | h1977
                      · linarith only [h1345, h1863, h1977, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1979 | h1979
                        · linarith only [h1861, h1863, h1979, hlam]
                        · rcases h1bigk with h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c | h1981c
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h0, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h903, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1345, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1450, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            rcases p1981_3 (m.d 0 1) (by simp) with h1987 | h1987
                            · linarith only [h1987, hlam, p1981_0]
                            · rcases p1981_3 (m.d 1 2) (by simp) with h1989 | h1989
                              · rcases p1981_3 (m.d 1 3) (by simp) with h1990 | h1990
                                · linarith only [h1858, h1990, hlam]
                                · linarith only [h1990, h903, hlam]
                              · linarith only [h1989, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h903, hc01, hc12, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1581, h1861, h903, hc01, hc12, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            rcases p1981_3 (m.d 0 1) (by simp) with h1998 | h1998
                            · linarith only [h1998, hlam, p1981_0]
                            · rcases p1981_3 (m.d 1 2) (by simp) with h2000 | h2000
                              · rcases p1981_3 (m.d 1 3) (by simp) with h2001 | h2001
                                · rcases p1981_3 (m.d 1 4) (by simp) with h2002 | h2002
                                  · linarith only [h1861, h2002, hlam]
                                  · linarith only [h1345, h2002, hlam]
                                · linarith only [h2001, hlam, p1981_0]
                              · linarith only [h0, h2000, hlam]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1858, hlam, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1581, h1861, h903, hc01, hc13, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1581, h1858, h1862, h1979, h903, hc01, hc12, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1863, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1859, hlam, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1861, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1863, hlam, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            rcases p1981_3 (m.d 0 1) (by simp) with h2016 | h2016
                            · linarith only [h2016, hlam, p1981_0]
                            · rcases p1981_3 (m.d 1 2) (by simp) with h2018 | h2018
                              · rcases p1981_3 (m.d 1 3) (by simp) with h2019 | h2019
                                · rcases p1981_3 (m.d 1 4) (by simp) with h2020 | h2020
                                  · linarith only [h1863, h2020, hlam]
                                  · linarith only [h1345, h2020, hlam]
                                · linarith only [h2019, h903, hlam]
                              · linarith only [h0, h2018, hlam]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1860, hlam, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1862, hlam, p1981_0]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [h1345, hc01, hc15, hlam, hphi, p1981_1]
                          · have p1981_0 := h1981c.1
                            have p1981_1 := h1981c.2.1
                            have p1981_2 := h1981c.2.2.1
                            have p1981_3 := h1981c.2.2.2
                            linarith only [hlam, p1981_0]
              · linarith only [h1581, h1861, h1862, h903, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2030 | h2030
              · linarith only [h1794, h1861, h2030, h903, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2032 | h2032
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2033 | h2033
                  · linarith only [h1580, h2033, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2035 | h2035
                    · linarith only [h1580, h1794, h2035, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2037 | h2037
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2038 | h2038
                        · rcases h1bigk with h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c | h2039c
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h0, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h903, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1345, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1450, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            rcases p2039_3 (m.d 0 1) (by simp) with h2045 | h2045
                            · linarith only [h2045, hlam, p2039_0]
                            · rcases p2039_3 (m.d 1 2) (by simp) with h2047 | h2047
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2048 | h2048
                                · linarith only [h1858, h2048, hlam]
                                · linarith only [h2048, h903, hlam]
                              · linarith only [h2047, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h903, hc01, hc12, hlam, hphi, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1345, hc01, hc12, hlam, hphi, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h2030, h2038, hc01, hc34, hlam, hphi, ht12, ht23, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1858, hlam, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1861, hlam, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h2030, hlam, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            rcases p2039_3 (m.d 0 1) (by simp) with h2061 | h2061
                            · linarith only [h2061, hlam, p2039_0]
                            · rcases p2039_3 (m.d 1 2) (by simp) with h2063 | h2063
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2064 | h2064
                                · linarith only [h1861, h2064, hlam]
                                · linarith only [h2064, h903, hlam]
                              · linarith only [h0, h2063, hlam]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1859, hlam, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h903, hc01, hc14, hlam, hphi, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1861, h2030, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            rcases p2039_3 (m.d 0 1) (by simp) with h2072 | h2072
                            · linarith only [h2072, hlam, p2039_0]
                            · rcases p2039_3 (m.d 1 2) (by simp) with h2074 | h2074
                              · rcases p2039_3 (m.d 1 3) (by simp) with h2075 | h2075
                                · linarith only [h2030, h2075, hlam]
                                · linarith only [h2075, h903, hlam]
                              · linarith only [h0, h2074, hlam]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h1860, hlam, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h903, hc01, hc15, hlam, hphi, p2039_1]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [h2032, hlam, p2039_0]
                          · have p2039_0 := h2039c.1
                            have p2039_1 := h2039c.2.1
                            have p2039_2 := h2039c.2.2.1
                            have p2039_3 := h2039c.2.2.2
                            linarith only [hlam, p2039_0]
                        · linarith only [h1345, h1861, h2037, h2038, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2084 | h2084
                        · rcases h1bigk with h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c | h2085c
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h0, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h903, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1345, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1450, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            rcases p2085_3 (m.d 0 1) (by simp) with h2091 | h2091
                            · linarith only [h2091, hlam, p2085_0]
                            · rcases p2085_3 (m.d 1 2) (by simp) with h2093 | h2093
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2094 | h2094
                                · linarith only [h1858, h2094, hlam]
                                · linarith only [h2094, h903, hlam]
                              · linarith only [h2093, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h903, hc01, hc12, hlam, hphi, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h2032, h2037, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p2085_1, u4ehi2]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1450, hc01, hc12, hlam, hphi, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1861, hc01, hc34, hlam, hphi, ht12, ht23, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1858, hlam, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1861, hlam, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h2030, hlam, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            rcases p2085_3 (m.d 0 1) (by simp) with h2107 | h2107
                            · linarith only [h2107, hlam, p2085_0]
                            · rcases p2085_3 (m.d 1 2) (by simp) with h2109 | h2109
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2110 | h2110
                                · linarith only [h1861, h2110, hlam]
                                · linarith only [h2110, h903, hlam]
                              · linarith only [h0, h2109, hlam]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1859, hlam, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h903, hc01, hc14, hlam, hphi, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1861, h2032, h2037, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p2085_1, u4ehi2]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            rcases p2085_3 (m.d 0 1) (by simp) with h2118 | h2118
                            · linarith only [h2118, hlam, p2085_0]
                            · rcases p2085_3 (m.d 1 2) (by simp) with h2120 | h2120
                              · rcases p2085_3 (m.d 1 3) (by simp) with h2121 | h2121
                                · linarith only [h2030, h2121, hlam]
                                · linarith only [h2121, h903, hlam]
                              · linarith only [h0, h2120, hlam]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h1860, hlam, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h903, hc01, hc15, hlam, hphi, p2085_1]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [h2032, hlam, p2085_0]
                          · have p2085_0 := h2085c.1
                            have p2085_1 := h2085c.2.1
                            have p2085_2 := h2085c.2.2.1
                            have p2085_3 := h2085c.2.2.2
                            linarith only [hlam, p2085_0]
                        · linarith only [h1861, h2084, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2130 | h2130
                  · linarith only [h1580, h1861, h2130, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2132 | h2132
                    · linarith only [h1580, h1794, h2132, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2134 | h2134
                      · linarith only [h1345, h2032, h2134, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2136 | h2136
                        · linarith only [h1345, h2032, h2136, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h1861, h2136, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2139 | h2139
            · linarith only [h1581, h1858, h1860, h2139, h903, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2141 | h2141
              · linarith only [h1794, h1858, h1860, h2141, h903, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2143 | h2143
                · linarith only [h1859, h1860, h2143, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2145 | h2145
                  · linarith only [h0, h1580, h1860, h2145, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2147 | h2147
                    · linarith only [h1580, h2141, h2147, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2149 | h2149
                      · linarith only [h1859, h1860, h2143, h2147, h2149, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                      · linarith only [h1859, h1860, h2149, hc45, hlam, hphi, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2152 | h2152
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2153 | h2153
            · linarith only [h1581, h1858, h1859, h2153, h903, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2155 | h2155
              · linarith only [h1794, h1858, h1859, h2155, h903, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2157 | h2157
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2158 | h2158
                  · linarith only [h1580, h2153, h2158, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2160 | h2160
                    · linarith only [h0, h1580, h1859, h2155, h2158, h2160, h903, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2162 | h2162
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2163 | h2163
                        · rcases h1bigk with h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c | h2164c
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h0, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h903, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1345, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1450, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2158, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2155, h2158, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2155, hc01, hc35, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1858, hlam, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2153, hlam, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2155, hlam, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            rcases p2164_3 (m.d 0 1) (by simp) with h2180 | h2180
                            · linarith only [h2180, hlam, p2164_0]
                            · rcases p2164_3 (m.d 1 2) (by simp) with h2182 | h2182
                              · linarith only [h1859, h2182, hlam]
                              · linarith only [h0, h2182, hlam]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2152, h2162, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2164_1, u4ehi4]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2158, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1450, h1859, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2152, h2158, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2152, hlam, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h1859, h2152, h2158, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2164_1]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [h2157, hlam, p2164_0]
                          · have p2164_0 := h2164c.1
                            have p2164_1 := h2164c.2.1
                            have p2164_2 := h2164c.2.2.1
                            have p2164_3 := h2164c.2.2.2
                            linarith only [hlam, p2164_0]
                        · linarith only [h1859, h2152, h2158, h2162, h2163, hlam]
                      · linarith only [h0, h1580, h1859, h2162, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1859, h2152, h2157, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2197 | h2197
            · linarith only [h1581, h1858, h2152, h2197, h903, hc01, hc25, hlam, hphi, ht12]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2199 | h2199
              · linarith only [h1794, h1858, h2152, h2199, h903, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2201 | h2201
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2202 | h2202
                  · linarith only [h1580, h2197, h2202, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2204 | h2204
                    · linarith only [h0, h1450, h1580, h1859, h2199, h2202, h2204, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2206 | h2206
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2207 | h2207
                        · rcases h1bigk with h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c | h2208c
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h0, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h903, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1345, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1450, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2152, h2202, h2206, hc01, hc34, hlam, hphi, ht12, ht23, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2152, h2202, h2206, h903, hc03, hc34, hlam, hphi, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1859, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2152, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1858, h2152, h2202, h2206, hc01, hc34, hlam, hphi, ht12, ht23, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1858, hlam, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2197, hlam, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2199, hlam, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 1) (by simp) with h2224 | h2224
                            · linarith only [h2224, hlam, p2208_0]
                            · rcases p2208_3 (m.d 1 2) (by simp) with h2226 | h2226
                              · linarith only [h1859, h2226, hlam]
                              · linarith only [h0, h2226, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h0, hc01, hc14, hlam, hphi, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1859, h2202, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1858, h1859, h2152, h2202, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            rcases p2208_3 (m.d 0 1) (by simp) with h2233 | h2233
                            · linarith only [h2233, hlam, p2208_0]
                            · rcases p2208_3 (m.d 1 2) (by simp) with h2235 | h2235
                              · linarith only [h2152, h2235, hlam]
                              · linarith only [h0, h2235, hlam]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h1858, h903, hc01, hc15, hlam, hphi, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2152, h2202, h2206, h903, hc01, hc34, hlam, hphi, ht12, ht23, p2208_1]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [h2201, hlam, p2208_0]
                          · have p2208_0 := h2208c.1
                            have p2208_1 := h2208c.2.1
                            have p2208_2 := h2208c.2.2.1
                            have p2208_3 := h2208c.2.2.2
                            linarith only [hlam, p2208_0]
                        · linarith only [h1858, h1859, h2202, h2207, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h1858, h1859, h2201, h2206, h903, hc01, hc14, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2244 | h2244
                  · linarith only [h0, h1580, h2152, h2244, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2246 | h2246
                    · linarith only [h0, h1580, h1794, h1859, h2201, h2246, hc03, hc45, hlam, hphi, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2248 | h2248
                      · linarith only [h1858, h1859, h2201, h2248, h903, hc01, hc24, hlam, hphi, ht12]
                      · linarith only [h1858, h1859, h2248, h903, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h1580, h1858, hlam]

end R2N4
