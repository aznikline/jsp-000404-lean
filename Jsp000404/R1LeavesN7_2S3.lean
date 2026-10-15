import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5020000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s9_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h1352 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h1513 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h1627 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h1628 | h1628
  · rcases m.htr 1 4 5 (by decide) (by decide) with h1629 | h1629
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1630 | h1630
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1631 | h1631
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1632 | h1632
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1633 | h1633
            · rcases h0bigk with h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c | h1634c
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h1, h1627, h1633, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h1, h1627, h1633, hc01, hc45, hlam, hphi, ht0b, ht5b, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1638 | h1638
                · rcases p1634_3 (m.d 0 2) (by simp) with h1639 | h1639
                  · linarith only [h0, h1639, hlam]
                  · linarith only [h1639, h5, hlam]
                · linarith only [h1638, h2, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1643 | h1643
                · rcases p1634_3 (m.d 0 2) (by simp) with h1644 | h1644
                  · linarith only [h0, h1644, hlam]
                  · linarith only [h1644, h6, hlam]
                · linarith only [h1643, h3, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h0, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h10, h1627, h1633, h4, hc02, hc45, hlam, hphi, ht0b, ht5b, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1651 | h1651
                · rcases p1634_3 (m.d 0 2) (by simp) with h1652 | h1652
                  · rcases p1634_3 (m.d 0 3) (by simp) with h1653 | h1653
                    · linarith only [h1653, h4, hlam]
                    · linarith only [h1653, h7, hlam]
                  · linarith only [h1652, h5, hlam]
                · linarith only [h1651, h2, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1658 | h1658
                · rcases p1634_3 (m.d 0 2) (by simp) with h1659 | h1659
                  · rcases p1634_3 (m.d 0 3) (by simp) with h1660 | h1660
                    · linarith only [h1660, h4, hlam]
                    · linarith only [h1660, h8, hlam]
                  · linarith only [h1659, h6, hlam]
                · linarith only [h1658, h3, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h1, hlam, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h4, hlam, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1668 | h1668
                · rcases p1634_3 (m.d 0 2) (by simp) with h1669 | h1669
                  · rcases p1634_3 (m.d 0 3) (by simp) with h1670 | h1670
                    · rcases p1634_3 (m.d 0 4) (by simp) with h1671 | h1671
                      · linarith only [h1671, h7, hlam]
                      · rcases p1634_3 (m.d 0 5) (by simp) with h1673 | h1673
                        · linarith only [h1673, h8, hlam]
                        · rcases h2bigk with h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c | h1675c
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1513, h1632, h4, h5, hlam, p1634_1, p1675_2]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, h10, h1627, h1633, hc01, hc45, hlam, hphi, ht0b, ht5b, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            rcases p1675_3 (m.d 0 2) (by simp) with h1679 | h1679
                            · rcases p1675_3 (m.d 1 2) (by simp) with h1680 | h1680
                              · linarith only [h0, h1680, hlam]
                              · rcases p1675_3 (m.d 2 3) (by simp) with h1682 | h1682
                                · linarith only [h1682, h4, hlam]
                                · linarith only [h1630, h1682, hlam]
                            · linarith only [h1679, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            rcases p1675_3 (m.d 0 2) (by simp) with h1686 | h1686
                            · rcases p1675_3 (m.d 1 2) (by simp) with h1687 | h1687
                              · linarith only [h0, h1687, hlam]
                              · rcases p1675_3 (m.d 2 3) (by simp) with h1689 | h1689
                                · linarith only [h1689, h4, hlam]
                                · linarith only [h1631, h1689, hlam]
                            · linarith only [h1686, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h10, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1352, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1513, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h4, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            rcases p1675_3 (m.d 0 2) (by simp) with h1699 | h1699
                            · rcases p1675_3 (m.d 1 2) (by simp) with h1700 | h1700
                              · linarith only [h1700, hlam, p1675_0]
                              · rcases p1675_3 (m.d 2 3) (by simp) with h1702 | h1702
                                · rcases p1675_3 (m.d 2 4) (by simp) with h1703 | h1703
                                  · linarith only [h1630, h1703, hlam]
                                  · linarith only [h1352, h1703, hlam]
                                · linarith only [h1702, hlam, p1675_0]
                            · linarith only [h0, h1699, hlam]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1513, h1632, hc12, hc23, hlam, hphi, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, h1513, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h5, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1634_1, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1630, hlam, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, h1513, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1634_1, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h6, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h0, h4, h6, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1634_1, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1631, hlam, p1675_1]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [h1632, hlam, p1675_0]
                          · have p1675_0 := h1675c.1
                            have p1675_1 := h1675c.2.1
                            have p1675_2 := h1675c.2.2.1
                            have p1675_3 := h1675c.2.2.2
                            linarith only [hlam, p1675_0]
                    · linarith only [h1670, h7, hlam]
                  · linarith only [h1669, h5, hlam]
                · linarith only [h1668, h2, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1724 | h1724
                · rcases p1634_3 (m.d 0 2) (by simp) with h1725 | h1725
                  · rcases p1634_3 (m.d 0 3) (by simp) with h1726 | h1726
                    · rcases p1634_3 (m.d 0 4) (by simp) with h1727 | h1727
                      · linarith only [h1727, h7, hlam]
                      · linarith only [h1727, h9, hlam]
                    · linarith only [h1726, h8, hlam]
                  · linarith only [h1725, h6, hlam]
                · linarith only [h1724, h3, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h2, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h5, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h7, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                rcases p1634_3 (m.d 0 1) (by simp) with h1737 | h1737
                · rcases p1634_3 (m.d 0 2) (by simp) with h1738 | h1738
                  · rcases p1634_3 (m.d 0 3) (by simp) with h1739 | h1739
                    · rcases p1634_3 (m.d 0 4) (by simp) with h1740 | h1740
                      · rcases p1634_3 (m.d 0 5) (by simp) with h1741 | h1741
                        · linarith only [h1741, h9, hlam]
                        · rcases h2bigk with h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c | h1743c
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1513, h5, h6, hlam, p1634_1, p1743_2]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h10, h1627, h1633, hc02, hc45, hlam, hphi, ht0b, ht5b, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            rcases p1743_3 (m.d 0 2) (by simp) with h1747 | h1747
                            · rcases p1743_3 (m.d 1 2) (by simp) with h1748 | h1748
                              · linarith only [h0, h1748, hlam]
                              · rcases p1743_3 (m.d 2 3) (by simp) with h1750 | h1750
                                · linarith only [h1750, h4, hlam]
                                · linarith only [h1630, h1750, hlam]
                            · linarith only [h1747, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            rcases p1743_3 (m.d 0 2) (by simp) with h1754 | h1754
                            · rcases p1743_3 (m.d 1 2) (by simp) with h1755 | h1755
                              · linarith only [h0, h1755, hlam]
                              · rcases p1743_3 (m.d 2 3) (by simp) with h1757 | h1757
                                · linarith only [h1757, h4, hlam]
                                · linarith only [h1631, h1757, hlam]
                            · linarith only [h1754, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h0, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h10, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1352, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1513, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h4, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            rcases p1743_3 (m.d 0 2) (by simp) with h1767 | h1767
                            · rcases p1743_3 (m.d 1 2) (by simp) with h1768 | h1768
                              · linarith only [h1768, hlam, p1743_0]
                              · rcases p1743_3 (m.d 2 3) (by simp) with h1770 | h1770
                                · rcases p1743_3 (m.d 2 4) (by simp) with h1771 | h1771
                                  · linarith only [h1630, h1771, hlam]
                                  · linarith only [h1352, h1771, hlam]
                                · linarith only [h1770, hlam, p1743_0]
                            · linarith only [h0, h1767, hlam]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1352, hc12, hc23, hlam, hphi, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h0, h1513, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h5, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            rcases p1743_3 (m.d 0 2) (by simp) with h1780 | h1780
                            · rcases p1743_3 (m.d 1 2) (by simp) with h1781 | h1781
                              · linarith only [h1781, hlam, p1743_0]
                              · rcases p1743_3 (m.d 2 3) (by simp) with h1783 | h1783
                                · rcases p1743_3 (m.d 2 4) (by simp) with h1784 | h1784
                                  · rcases p1743_3 (m.d 2 5) (by simp) with h1785 | h1785
                                    · linarith only [h1632, h1785, hlam]
                                    · linarith only [h1513, h1785, hlam]
                                  · linarith only [h1784, hlam, p1743_0]
                                · linarith only [h10, h1783, hlam]
                            · linarith only [h0, h1780, hlam]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1630, hlam, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1513, hc12, hc24, hlam, hphi, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h6, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h6, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1634_1, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1631, hlam, p1743_1]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [h1632, hlam, p1743_0]
                          · have p1743_0 := h1743c.1
                            have p1743_1 := h1743c.2.1
                            have p1743_2 := h1743c.2.2.1
                            have p1743_3 := h1743c.2.2.2
                            linarith only [hlam, p1743_0]
                      · linarith only [h1740, h9, hlam]
                    · linarith only [h1739, h8, hlam]
                  · linarith only [h1738, h6, hlam]
                · linarith only [h1737, h3, hlam]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h3, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h6, hlam, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h8, hlam, p1634_0]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [h9, hlam, p1634_1]
              · have p1634_0 := h1634c.1
                have p1634_1 := h1634c.2.1
                have p1634_2 := h1634c.2.2.1
                have p1634_3 := h1634c.2.2.2
                linarith only [hlam, p1634_0]
            · rcases h0bigk with h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c | h1808c
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1633, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1633, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1633, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                rcases p1808_3 (m.d 0 1) (by simp) with h1813 | h1813
                · rcases p1808_3 (m.d 0 2) (by simp) with h1814 | h1814
                  · linarith only [h0, h1814, hlam]
                  · linarith only [h1814, h6, hlam]
                · linarith only [h1813, h3, hlam]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h0, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1, h1627, h1629, h1633, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h0, h1629, h1633, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                rcases p1808_3 (m.d 0 1) (by simp) with h1822 | h1822
                · rcases p1808_3 (m.d 0 2) (by simp) with h1823 | h1823
                  · rcases p1808_3 (m.d 0 3) (by simp) with h1824 | h1824
                    · linarith only [h1824, h4, hlam]
                    · linarith only [h1824, h8, hlam]
                  · linarith only [h1823, h6, hlam]
                · linarith only [h1822, h3, hlam]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1, hlam, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h4, hlam, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h1352, h1629, h1633, h5, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                rcases p1808_3 (m.d 0 1) (by simp) with h1833 | h1833
                · rcases p1808_3 (m.d 0 2) (by simp) with h1834 | h1834
                  · rcases p1808_3 (m.d 0 3) (by simp) with h1835 | h1835
                    · rcases p1808_3 (m.d 0 4) (by simp) with h1836 | h1836
                      · linarith only [h1836, h7, hlam]
                      · linarith only [h1836, h9, hlam]
                    · linarith only [h1835, h8, hlam]
                  · linarith only [h1834, h6, hlam]
                · linarith only [h1833, h3, hlam]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h2, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h5, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h7, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                rcases p1808_3 (m.d 0 1) (by simp) with h1846 | h1846
                · rcases p1808_3 (m.d 0 2) (by simp) with h1847 | h1847
                  · rcases p1808_3 (m.d 0 3) (by simp) with h1848 | h1848
                    · rcases p1808_3 (m.d 0 4) (by simp) with h1849 | h1849
                      · rcases p1808_3 (m.d 0 5) (by simp) with h1850 | h1850
                        · linarith only [h1850, h9, hlam]
                        · rcases h2bigk with h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c | h1852c
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1513, h4, h6, h7, hlam, p1808_1, p1852_2]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h10, h1627, h1629, h1633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1352, h1629, h1633, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1857 | h1857
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1858 | h1858
                              · linarith only [h0, h1858, hlam]
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1860 | h1860
                                · linarith only [h1860, h4, hlam]
                                · linarith only [h1631, h1860, hlam]
                            · linarith only [h1857, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h10, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1352, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1513, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h4, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1870 | h1870
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1871 | h1871
                              · linarith only [h1871, hlam, p1852_0]
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1873 | h1873
                                · rcases p1852_3 (m.d 2 4) (by simp) with h1874 | h1874
                                  · linarith only [h1630, h1874, hlam]
                                  · linarith only [h1352, h1874, hlam]
                                · linarith only [h1873, hlam, p1852_0]
                            · linarith only [h0, h1870, hlam]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1352, h1513, h1629, h1633, h4, h6, h7, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p1808_1, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h1513, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h5, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            rcases p1852_3 (m.d 0 2) (by simp) with h1883 | h1883
                            · rcases p1852_3 (m.d 1 2) (by simp) with h1884 | h1884
                              · linarith only [h1884, hlam, p1852_0]
                              · rcases p1852_3 (m.d 2 3) (by simp) with h1886 | h1886
                                · rcases p1852_3 (m.d 2 4) (by simp) with h1887 | h1887
                                  · rcases p1852_3 (m.d 2 5) (by simp) with h1888 | h1888
                                    · linarith only [h1632, h1888, hlam]
                                    · linarith only [h1513, h1888, hlam]
                                  · linarith only [h1887, hlam, p1852_0]
                                · linarith only [h10, h1886, hlam]
                            · linarith only [h0, h1883, hlam]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1630, hlam, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1513, hc12, hc24, hlam, hphi, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h6, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1808_1, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1631, hlam, p1852_1]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [h1632, hlam, p1852_0]
                          · have p1852_0 := h1852c.1
                            have p1852_1 := h1852c.2.1
                            have p1852_2 := h1852c.2.2.1
                            have p1852_3 := h1852c.2.2.2
                            linarith only [hlam, p1852_0]
                      · linarith only [h1849, h9, hlam]
                    · linarith only [h1848, h8, hlam]
                  · linarith only [h1847, h6, hlam]
                · linarith only [h1846, h3, hlam]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h3, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h6, hlam, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h8, hlam, p1808_0]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [h9, hlam, p1808_1]
              · have p1808_0 := h1808c.1
                have p1808_1 := h1808c.2.1
                have p1808_2 := h1808c.2.2.1
                have p1808_3 := h1808c.2.2.2
                linarith only [hlam, p1808_0]
          · linarith only [h1, h1352, h1627, h1629, h1632, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · linarith only [h10, h1628, h1631, hlam]
      · linarith only [h10, h1627, h1630, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h1914 | h1914
      · rcases m.htr 2 3 5 (by decide) (by decide) with h1915 | h1915
        · rcases m.htr 2 4 5 (by decide) (by decide) with h1916 | h1916
          · rcases m.htr 3 4 5 (by decide) (by decide) with h1917 | h1917
            · linarith only [h1, h1627, h1629, h1917, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
            · rcases h0bigk with h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c | h1919c
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1352, h1629, h1916, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1352, h1629, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1352, h1629, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                rcases p1919_3 (m.d 0 1) (by simp) with h1924 | h1924
                · rcases p1919_3 (m.d 0 2) (by simp) with h1925 | h1925
                  · linarith only [h0, h1925, hlam]
                  · linarith only [h1925, h6, hlam]
                · linarith only [h1924, h3, hlam]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h0, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1352, h1629, h1914, h1916, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h0, h1352, h1629, h1916, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                rcases p1919_3 (m.d 0 1) (by simp) with h1933 | h1933
                · rcases p1919_3 (m.d 0 2) (by simp) with h1934 | h1934
                  · rcases p1919_3 (m.d 0 3) (by simp) with h1935 | h1935
                    · linarith only [h1935, h4, hlam]
                    · linarith only [h1935, h8, hlam]
                  · linarith only [h1934, h6, hlam]
                · linarith only [h1933, h3, hlam]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1, hlam, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h4, hlam, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h1352, h1629, h1916, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                rcases p1919_3 (m.d 0 1) (by simp) with h1944 | h1944
                · rcases p1919_3 (m.d 0 2) (by simp) with h1945 | h1945
                  · rcases p1919_3 (m.d 0 3) (by simp) with h1946 | h1946
                    · rcases p1919_3 (m.d 0 4) (by simp) with h1947 | h1947
                      · linarith only [h1947, h7, hlam]
                      · linarith only [h1947, h9, hlam]
                    · linarith only [h1946, h8, hlam]
                  · linarith only [h1945, h6, hlam]
                · linarith only [h1944, h3, hlam]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h2, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h5, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h7, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                rcases p1919_3 (m.d 0 1) (by simp) with h1957 | h1957
                · rcases p1919_3 (m.d 0 2) (by simp) with h1958 | h1958
                  · rcases p1919_3 (m.d 0 3) (by simp) with h1959 | h1959
                    · rcases p1919_3 (m.d 0 4) (by simp) with h1960 | h1960
                      · rcases p1919_3 (m.d 0 5) (by simp) with h1961 | h1961
                        · linarith only [h1961, h9, hlam]
                        · rcases h2bigk with h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c | h1963c
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1352, h1629, h1914, h1916, h4, hlam, p1963_2]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1352, h1629, h1914, h1916, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h0, h1352, h1629, h1916, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            rcases p1963_3 (m.d 0 2) (by simp) with h1968 | h1968
                            · rcases p1963_3 (m.d 1 2) (by simp) with h1969 | h1969
                              · linarith only [h0, h1969, hlam]
                              · rcases p1963_3 (m.d 2 3) (by simp) with h1971 | h1971
                                · linarith only [h1971, h4, hlam]
                                · linarith only [h1915, h1971, hlam]
                            · linarith only [h1968, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h0, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h10, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1352, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1513, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h4, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            rcases p1963_3 (m.d 0 2) (by simp) with h1981 | h1981
                            · rcases p1963_3 (m.d 1 2) (by simp) with h1982 | h1982
                              · linarith only [h1982, hlam, p1963_0]
                              · rcases p1963_3 (m.d 2 3) (by simp) with h1984 | h1984
                                · rcases p1963_3 (m.d 2 4) (by simp) with h1985 | h1985
                                  · linarith only [h1914, h1985, hlam]
                                  · linarith only [h1352, h1985, hlam]
                                · linarith only [h1984, hlam, p1963_0]
                            · linarith only [h0, h1981, hlam]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1352, h1629, h1916, hc12, hc23, hlam, hphi, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h0, h1352, h1629, h1916, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h5, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            rcases p1963_3 (m.d 0 2) (by simp) with h1994 | h1994
                            · rcases p1963_3 (m.d 1 2) (by simp) with h1995 | h1995
                              · linarith only [h1995, hlam, p1963_0]
                              · rcases p1963_3 (m.d 2 3) (by simp) with h1997 | h1997
                                · rcases p1963_3 (m.d 2 4) (by simp) with h1998 | h1998
                                  · rcases p1963_3 (m.d 2 5) (by simp) with h1999 | h1999
                                    · linarith only [h1916, h1999, hlam]
                                    · linarith only [h1513, h1999, hlam]
                                  · linarith only [h1998, hlam, p1963_0]
                                · linarith only [h10, h1997, hlam]
                            · linarith only [h0, h1994, hlam]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1914, hlam, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1352, h1629, h1916, hc12, hc24, hlam, hphi, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h6, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1919_1, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1915, hlam, p1963_1]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [h1916, hlam, p1963_0]
                          · have p1963_0 := h1963c.1
                            have p1963_1 := h1963c.2.1
                            have p1963_2 := h1963c.2.2.1
                            have p1963_3 := h1963c.2.2.2
                            linarith only [hlam, p1963_0]
                      · linarith only [h1960, h9, hlam]
                    · linarith only [h1959, h8, hlam]
                  · linarith only [h1958, h6, hlam]
                · linarith only [h1957, h3, hlam]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h3, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h6, hlam, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h8, hlam, p1919_0]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [h9, hlam, p1919_1]
              · have p1919_0 := h1919c.1
                have p1919_1 := h1919c.2.1
                have p1919_2 := h1919c.2.2.1
                have p1919_3 := h1919c.2.2.2
                linarith only [hlam, p1919_0]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2022 | h2022
            · linarith only [h1352, h1916, h2022, hc12, hc34, hlam, hphi, ht23]
            · rcases h0bigk with h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c | h2024c
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h10, h1628, h4, hc01, hc35, hlam, hphi, ht0b, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h1513, h1916, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h1513, h1916, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h1352, h1916, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, h1352, h1916, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, h1352, h1916, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, h1352, h1916, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h1, hlam, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h4, hlam, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h1352, h1916, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, h1352, h1916, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h2, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h5, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h7, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h0, h1352, h1916, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h3, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h6, hlam, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h8, hlam, p2024_0]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [h9, hlam, p2024_1]
              · have p2024_0 := h2024c.1
                have p2024_1 := h2024c.2.1
                have p2024_2 := h2024c.2.2.1
                have p2024_3 := h2024c.2.2.2
                linarith only [hlam, p2024_0]
        · linarith only [h10, h1628, h1915, hlam]
      · linarith only [h10, h1627, h1914, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h2052 | h2052
    · linarith only [h1627, h1628, h2052, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2054 | h2054
      · rcases m.htr 2 3 5 (by decide) (by decide) with h2055 | h2055
        · linarith only [h0, h1627, h1628, h2055, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 2 4 5 (by decide) (by decide) with h2057 | h2057
          · linarith only [h0, h2052, h2054, h2055, h2057, h4, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 3 4 5 (by decide) (by decide) with h2059 | h2059
            · linarith only [h1352, h1627, h2057, h2059, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases h0bigk with h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c | h2061c
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h4, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h7, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h0, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h7, h9, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h0, h1352, h2054, h2055, h2059, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h0, h1352, h2054, h2055, h2059, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1, hlam, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h4, hlam, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h9, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h0, h1352, h2054, h2055, h2059, h4, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h2, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h5, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h7, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h1352, h2054, h2055, h2059, h9, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h3, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h6, hlam, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h8, hlam, p2061_0]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [h9, hlam, p2061_1]
              · have p2061_0 := h2061c.1
                have p2061_1 := h2061c.2.1
                have p2061_2 := h2061c.2.2.1
                have p2061_3 := h2061c.2.2.2
                linarith only [hlam, p2061_0]
      · linarith only [h10, h1627, h2054, hlam]

end R2N4
